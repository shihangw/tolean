package divide

func Quo(a int, b int) int {
return a / b
}

func Rem(a int, b int) int {
return a % b
}

func Mean(total int, count int) int {
mean := total / count
mean %= 1000
return mean
}

func Ratio(a int, b int) int {
if a/b > 2 {
return a % (b - 1)
}
return 0
}

func Halve(n int) int {
return n / 2
}
