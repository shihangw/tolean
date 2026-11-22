package main

import "fmt"

func find(xs []int, key int) int {
	for _, x := range xs {
		if x == key {
			return x
		}
	}
	return -1
}

func main() { fmt.Println(find([]int{1, 2, 3, 4}, 3)) }
