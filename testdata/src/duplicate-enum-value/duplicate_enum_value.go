package duplicateenumvalue

type River string // want River:"^DefaultRiver,Yamuna,Ganga,Kaveri$"

const DefaultRiver = Ganga

const (
	Yamuna River = "Yamuna"
	Ganga  River = "Ganga"
	Kaveri River = "Kaveri"
)

type State int // want State:"^TamilNadu,Kerala,Karnataka,DefaultState$"

const (
	_ State = iota
	TamilNadu
	Kerala
	Karnataka
	DefaultState = TamilNadu
)

type Chart int // want Chart:"^Line,Area,Sunburst,Pie,circle$"

const (
	Line Chart = iota
	Area
	Sunburst
	Pie
	circle = Pie // NOTE: unexported
)

func _s(c Chart) {
	switch c { // want "^missing cases in switch of type Chart: Pie\\|circle$"
	case Line:
	case Sunburst:
	case Area:
	}
}
