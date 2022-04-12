package exhaustive

import (
	"fmt"
	"go/ast"
	"go/types"
	"sort"
	"strings"

	"golang.org/x/tools/go/analysis"
	"golang.org/x/tools/go/ast/inspector"
)

// structLiteralChecker returns a node visitor that checks exhaustiveness
// of struct literal statements for the supplied pass, and reports diagnostics
// for structs literal statements that are non-exhaustive. It expects to only
// see *ast.CompositeLit nodes.
func structLiteralChecker(pass *analysis.Pass, cfg structConfig) nodeVisitor {
	generated := make(map[*ast.File]bool)          // cached results
	comments := make(map[*ast.File]ast.CommentMap) // cached results

	return func(n ast.Node, push bool, stack []ast.Node) (bool, string) {
		if !push {
			// The proceed return value should not matter; it is ignored by
			// inspector package for pop calls.
			// Nevertheless, return true to be on the safe side for the future.
			return true, resultNotPush
		}

		file := stack[0].(*ast.File)

		// Determine if the file is a generated file, and save the result.
		// If it is a generated file, don't check the file.
		if _, ok := generated[file]; !ok {
			generated[file] = isGeneratedFile(file)
		}
		if generated[file] && !cfg.checkGeneratedFiles {
			// Don't check this file.
			// Return false because the children nodes of node `n` don't have to be checked.
			return false, resultGeneratedFile
		}

		structLiteral := n.(*ast.CompositeLit)

		typeInfo := pass.TypesInfo.Types[structLiteral]
		structTypeName, structType, ok := resolveStructType(typeInfo.Type)
		if !ok {
			return true, resultCompositeLitNotAStruct
		}

		if _, ok := comments[file]; !ok {
			comments[file] = ast.NewCommentMap(pass.Fset, file, file.Comments)
		}
		structComments := comments[file][structLiteral]
		if !containsEnforceDirective(structComments) {
			// Skip checking of this struct literal due to missing enforce directive comment.
			return true, resultStructNoEnforceComment
		}

		structFields := make([]string, 0, structType.NumFields())
		for i := 0; i < structType.NumFields(); i++ {
			structFields = append(structFields, structType.Field(i).Name())
		}

		// do struct literal and struct definition live in the same package?
		samePkg := true
		if structTypeName != nil {
			structPkg := structTypeName.Pkg()
			samePkg = structPkg == pass.Pkg
		}
		// we want to include unexported fields in the exhaustiveness check only if we're in the same package
		checkUnexported := samePkg
		checklist := makeStructChecklist(structFields, checkUnexported)
		isUnkeyedLit := analyzeStructLiteralFields(structLiteral, checklist.found)
		if isUnkeyedLit {
			return true, resultStructUnkeyedLiteral
		}

		if len(checklist.remaining()) == 0 {
			// All struct fields accounted for.
			// Nothing to report.
			return true, resultStructFieldsAccounted
		}
		pass.Report(makeStructDiagnostic(structLiteral, samePkg, structTypeName, checklist.remaining()))
		return true, resultReportedDiagnostic
	}
}

// structConfig is a configuration for checkStructLiterals.
type structConfig struct {
	checkGeneratedFiles bool
}

// resolveStructType resolves the struct type of the composite literal if it
// is a struct and the struct type name if the struct is not anonymous. If the
// struct is type aliased, this method will identify the bottom-level
// unwrapped struct type and type name
func resolveStructType(compositeLiteralType types.Type) (_ *types.TypeName, _ *types.Struct, isStruct bool) {
	t := compositeLiteralType
	for {
		switch v := t.(type) {
		case *types.Pointer:
			t = v.Elem()
		case *types.Struct:
			return nil, v, true
		case *types.Named:
			underlying := v.Underlying()
			if structType, ok := underlying.(*types.Struct); ok {
				return v.Obj(), structType, true
			}
			t = underlying
		default:
			return nil, nil, false
		}
	}
}

// checkStructLiterals checks exhaustiveness of struct literal fields for the
// supplied pass. It reports struct literals that are not exhaustive via
// pass.Report.
func checkStructLiterals(pass *analysis.Pass, inspect *inspector.Inspector, cfg structConfig) {
	f := structLiteralChecker(pass, cfg)

	inspect.WithStack([]ast.Node{&ast.CompositeLit{}}, func(n ast.Node, push bool, stack []ast.Node) bool {
		proceed, _ := f(n, push, stack)
		return proceed
	})
}

// analyzeStructLiteralFields analyzers the strings in the supplied struct
// literal. The found function is called for each field found in the struct
// literal.
// The isUnkeyedLiteral return value indicates whether the struct literal only
// has unkeyed fields, in which case the analyzer has nothing to do.
func analyzeStructLiteralFields(structLiteral *ast.CompositeLit, found func(fieldName string)) (isUnkeyedLiteral bool) {
	for _, elem := range structLiteral.Elts {
		keyValueElt, ok := elem.(*ast.KeyValueExpr)
		if !ok {
			return true
		}
		if keyValueElt.Key == nil {
			return true
		}
		found(keyValueElt.Key.(*ast.Ident).Name)
	}
	return false
}

// diagnosticStructTypeName returns a string representation of a struct type for
// use in reported diagnostics.
func diagnosticStructTypeName(structTyp *types.TypeName, samePkg bool) string {
	if structTyp == nil {
		return "(anonymous)"
	}
	if samePkg {
		return structTyp.Name()
	}
	return structTyp.Pkg().Name() + "." + structTyp.Name()
}

// A checklist holds a set of struct field names that have to be accounted
// for to satisfy exhaustiveness in a struct literal. The found method checks
// off struct fields from the set, based on constant value, when a struct
// field is encoutered in the struct literal.
//
// The remaining method returns the member names not accounted for.
type structChecklist struct {
	checkl map[string]struct{}
}

// Makes a "missing fields in struct" diagnostic.
// samePkg should be true if the struct definition and the struct literal are
// defined in the same package.
func makeStructDiagnostic(
	cl *ast.CompositeLit, samePkg bool, structTyp *types.TypeName,
	missingFields map[string]struct{},
) analysis.Diagnostic {
	var missingFieldArray []string
	for elem := range missingFields {
		missingFieldArray = append(missingFieldArray, elem)
	}
	sort.Strings(missingFieldArray)
	message := fmt.Sprintf("missing fields in struct of type %s: %s",
		diagnosticStructTypeName(structTyp, samePkg),
		strings.Join(missingFieldArray, ", "))

	return analysis.Diagnostic{
		Pos:     cl.Pos(),
		End:     cl.End(),
		Message: message,
	}
}

func makeStructChecklist(fieldNames []string, includeUnexported bool) *structChecklist {
	checkl := make(map[string]struct{})

	add := func(memberName string) {
		if memberName == "_" {
			// Blank field is effectively a directive to disallow "list-type" struct
			// initialization, but it can never be set
			return
		}
		if !ast.IsExported(memberName) && !includeUnexported {
			return
		}
		checkl[memberName] = struct{}{}
	}

	for _, name := range fieldNames {
		add(name)
	}

	return &structChecklist{
		checkl: checkl,
	}
}

func (c *structChecklist) found(fieldName string) {
	// Delete all of the same-valued names.
	delete(c.checkl, fieldName)
}

func (c *structChecklist) remaining() map[string]struct{} {
	return c.checkl
}
