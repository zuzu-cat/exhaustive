package fix

import "general/y"

func _k_func() {
	switch ReturnsDirection() { // want "^missing cases in switch of type Direction: S$"
	case N, E, W, directionInvalid:
	}
}

func _k_typeconversion() {
	// no function or method calls -- should add case clause for missing enum members

	var i int
	switch Direction(bar.IntWrapper(i)) { // want "^missing cases in switch of type Direction: S$"
	case N, E, W, directionInvalid:
	}
}

func _k_mix() {
	switch Direction(bar.IntWrapper(int(ReturnsDirection()))) { // want "^missing cases in switch of type Direction: S$"
	case N, E, W, directionInvalid:
	}
}

func _k_builtin() {
	var a, b []int
	switch Direction(copy(a, b)) { // want "^missing cases in switch of type Direction: S$"
	case N, E, W, directionInvalid:
	}
}