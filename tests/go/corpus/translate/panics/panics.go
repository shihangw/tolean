// Calls of functions that can panic. Quo panics when b is zero. Average and
// Scaled call it on the proved path; Total and Load call it from the
// string translation.
package panics

type Store interface {
	Get(key string) int
}

func Quo(a int, b int) int {
	return a / b
}

func Average(total int, count int) int {
	mean := Quo(total, count)
	if mean > 100 {
		mean = Quo(mean, 2)
	}
	return mean
}

func Scaled(a int, b int) int {
	var half int = Quo(a, 2)
	return Quo(half, b/2)
}

func Total(xs []int, n int) int {
	total := 0
	for _, x := range xs {
		total += Quo(x, n)
	}
	return total
}

func Load(s Store, key string, n int) int {
	v := s.Get(key)
	return Quo(v, n) + Total([]int{v}, n)
}
