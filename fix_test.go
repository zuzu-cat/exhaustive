package exhaustive

import (
	"go/ast"
	"go/parser"
	"go/token"
	"reflect"
	"strconv"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
)

func TestContainsFuncCall(t *testing.T) {
	cfg := &packages.Config{Mode: packages.NeedTypesInfo | packages.NeedTypes | packages.NeedSyntax}
	pkgs, err := packages.Load(cfg, "./testdata/funccall")
	assertNoError(t, err)

	pkg := pkgs[0]
	syn := pkg.Syntax[0]
	decl := syn.Decls[len(syn.Decls)-1].(*ast.GenDecl)

	if len(decl.Specs) != 8 {
		t.Errorf("wrong number of specs: want 8, got %d (either test or testdata file needs update?)", len(decl.Specs))
		return
	}

	for idx, spec := range decl.Specs {
		spec := spec.(*ast.ValueSpec)
		want, err := strconv.ParseBool(strings.Trim(spec.Comment.Text(), "\r\n"))
		if err != nil {
			// testdata file doesn't have comment in right format?
			t.Errorf("want nil error, got %v", err)
			continue
		}
		got := containsFuncCall(pkg.TypesInfo, spec.Values[0])
		if want != got {
			t.Errorf("[%d]: want %v, got %v", idx, want, got)
		}
	}
}

func TestHasImportWithPath(t *testing.T) {
	t.Run("does not have import", func(t *testing.T) {
		got := hasImportWithPath([]*ast.ImportSpec{
			{Path: &ast.BasicLit{Value: `"foo/bar"`}},
			{Path: &ast.BasicLit{Value: `"x/y"`}},
			{Path: &ast.BasicLit{Value: `"github.com/foo"`}},
		}, `"foo"`)
		if got {
			t.Errorf("unexpectedly true")
			return
		}
	})

	t.Run("has import", func(t *testing.T) {
		got := hasImportWithPath([]*ast.ImportSpec{
			{Path: &ast.BasicLit{Value: `"foo/bar"`}},
			{Path: &ast.BasicLit{Value: `"x/y"`}},
			{Path: &ast.BasicLit{Value: `"github.com/foo"`}},
		}, `"x/y"`)
		if !got {
			t.Errorf("unexpectedly false")
			return
		}
	})
}

func TestFlattenImportSpec(t *testing.T) {
	in := [][]*ast.ImportSpec{{
		{Path: &ast.BasicLit{Value: `"foo/bar"`}},
		{Path: &ast.BasicLit{Value: `"x/y"`}},
		{Path: &ast.BasicLit{Value: `"github.com/foo"`}},
	}, {
		{Path: &ast.BasicLit{Value: `"golang.org/x/net"`}},
	}, {
		{Path: &ast.BasicLit{Value: `"github.com/example"`}},
	}}

	got := flattenImportSpec(in)

	want := []*ast.ImportSpec{
		{Path: &ast.BasicLit{Value: `"foo/bar"`}},
		{Path: &ast.BasicLit{Value: `"x/y"`}},
		{Path: &ast.BasicLit{Value: `"github.com/foo"`}},
		{Path: &ast.BasicLit{Value: `"golang.org/x/net"`}},
		{Path: &ast.BasicLit{Value: `"github.com/example"`}},
	}
	if !reflect.DeepEqual(want, got) {
		t.Errorf("want %#v, got %#v", want, got)
		return
	}
}

func TestFirstImportDecl(t *testing.T) {
	t.Run("basic", func(t *testing.T) {
		const source = `package foo
import "fmt"
import ( "bytes" )`
		f, err := parser.ParseFile(token.NewFileSet(), "", source, parser.AllErrors)
		assertNoError(t, err)
		decl := firstImportDecl(f)
		if len(decl.Specs) != 1 {
			t.Errorf("wrong length %d", len(decl.Specs))
			return
		}
		if want, got := `"fmt"`, decl.Specs[0].(*ast.ImportSpec).Path.Value; want != got {
			t.Errorf("want %v, got %v", want, got)
			return
		}
	})

	t.Run("none", func(t *testing.T) {
		const source = `package foo`
		f, err := parser.ParseFile(token.NewFileSet(), "", source, parser.AllErrors)
		assertNoError(t, err)
		decl := firstImportDecl(f)
		if decl != nil {
			t.Errorf("unexpectedly found decl: %+v", decl)
			return
		}
	})
}

func TestFmtImportTextEdit(t *testing.T) {
	t.Run("file with existing imports", func(t *testing.T) {
		const source = `package foo

import ( "bytes" )

import ( "example.org/pkg" )`
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, "", source, parser.AllErrors)
		assertNoError(t, err)

		edit := fmtImportTextEdit(fset, f)
		gotText := string(edit.NewText)
		wantText := `import (
	"bytes"
	"fmt"
)`
		if wantText != gotText {
			t.Errorf("want %v, got %v", wantText, gotText)
			return
		}

		idx := strings.IndexByte(source, 'i') + 1
		wantPos := token.Pos(len(source[:idx]))
		if wantPos != edit.Pos {
			t.Errorf("Pos: want %v, got %v", wantPos, edit.Pos)
			return
		}

		idx = strings.IndexByte(source, ')') + 1
		wantEnd := token.Pos(len(source[:idx]) + 1) // when valid RParen exists go/token uses + 1
		if wantEnd != edit.End {
			t.Errorf("Pos: want %v, got %v", wantEnd, edit.End)
			return
		}
	})

	t.Run("file without existing imports", func(t *testing.T) {
		const source = `package foo`
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, "", source, parser.AllErrors)
		assertNoError(t, err)

		edit := fmtImportTextEdit(fset, f)
		gotText := string(edit.NewText)
		wantText := `import (
	"fmt"
)`
		if wantText != gotText {
			t.Errorf("want %v, got %v", wantText, gotText)
			return
		}

		wantPos := token.Pos(13)
		if wantPos != edit.Pos {
			t.Errorf("Pos: want %v, got %v", wantPos, edit.Pos)
			return
		}

		wantEnd := token.Pos(13)
		if wantEnd != edit.End {
			t.Errorf("Pos: want %v, got %v", wantEnd, edit.End)
			return
		}
	})
}