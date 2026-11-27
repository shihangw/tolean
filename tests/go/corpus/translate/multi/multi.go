package multi

func Swap(a int, b int) (int, int) {
	return b, a
}

func SumDiff(a int, b int) (int, int) {
	return a + b, a - b
}

func Triple(a int, s string) (int, bool, string) {
	return a * 2, a > 0, s + s
}

func Rotate(a int, b int, c int) int {
	a, b, c = b, c, a
	return a*100 + b*10 + c
}

func Combine(a int, b int) int {
	s, d := SumDiff(a, b)
	_, ok, _ := Triple(d, "x")
	if ok {
		return s / d
	}
	return s
}

func Again(a int, b int) (int, int) {
	x, y := Swap(a, b)
	x, y = SumDiff(x, y)
	return Swap(x, y)
}
