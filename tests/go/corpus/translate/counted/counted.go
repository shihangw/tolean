package counted

func Sum(total int) int {
	for i := 0; i < 10; i++ {
		total += i
	}
	return total
}

func Offset(total int) int {
	for i := 3; i < 6; i++ {
		total += i
	}
	return total
}

func Empty(total int) int {
	for i := 4; i < 2; i++ {
		total += i
	}
	return total
}

func Branch(total int, other int) int {
	for i := 0; i < 4; i++ {
		doubled := i * 2
		if i < 2 {
			total += doubled
		} else {
			other += i
		}
	}
	return total + other
}

func Wrap(total int) int {
	for i := 0; i < 2; i++ {
		total++
	}
	return total
}

func Limit(total int) int {
	for i := 0; i < 256; i++ {
		total++
	}
	return total
}

func Bounded(total int, n int) int {
for i := total; i < n+1; i++ {
total += i
}
return total
}

func Later(total int) int {
total++
for i := 0; i < 3; i++ {
total += i
}
total *= 2
return total
}

func Bytes(s string) int {
total := 0
for i := 0; i < len(s); i++ {
total += int(s[i])
}
return total
}

func Big(total int) int {
for i := 0; i < 1000; i++ {
total++
}
return total
}

func Nested(total int, n int) int {
if n > 0 {
for i := 0; i < n; i++ {
total += 2
}
} else {
total = 1
}
return total
}
