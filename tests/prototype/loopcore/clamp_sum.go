package main

import "fmt"

func clampSum(xs []int, limit int) int {
	s := 0
	for _, x := range xs {
		if x < 0 {
			continue
		}
		s += x
		if s > limit {
			break
		}
	}
	return s
}

func main() { fmt.Println(clampSum([]int{-1, 2, 3, 4}, 4)) }
