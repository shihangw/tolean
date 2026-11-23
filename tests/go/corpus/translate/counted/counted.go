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
