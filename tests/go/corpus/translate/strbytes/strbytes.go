package strbytes

func Size(s string) int {
return len(s)
}

func First(s string) int {
return int(s[0])
}

func At(s string, i int) int64 {
return int64(s[i]) + 1
}

func Less(a string, b string) bool {
return a < b
}

func Order(a string, b string) int {
if a <= b {
return -1
}
if a >= b && a > b {
return 1
}
return 0
}

func Joined(a string, b string) int {
return len(a + b)
}

func Pair(s string, i int, j int) int {
return int(s[i])*256 + int(s[j]) / (j - i)
}
