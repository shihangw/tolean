package syntaxonly

// The parser reads these; the translator refuses them.

func label(x any) string {
	switch t := x.(type) {
	case int, int64:
		return "number"
	case []rune:
		_ = t
	default:
		return "other"
	}
	switch x.(type) {
	}
	s, ok := x.(string)
	_, _ = s, ok
	return ""
}

func later() {
	defer cleanup()
	f := func(x int) (int, error) {
		return x, nil
	}
	g := func() {}
	_, _ = f, g
	var h func(int) bool = nil
	_ = h
}
