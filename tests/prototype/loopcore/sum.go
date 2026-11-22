package main

import "fmt"

func sum(xs []int) int {
	s := 0
	for _, x := range xs {
		s += x
	}
	return s
}

func main() { fmt.Println(sum([]int{1, 2, 3, 4})) }
