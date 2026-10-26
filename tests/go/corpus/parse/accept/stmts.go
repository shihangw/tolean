package stmts

func f(xs []int, m map[string]int) int {
	total := 0
	var x, y int
	var z = 3
	const k = 2
	type local struct{ v int }
	if err := check(); err != nil {
		return 0
	}
	if x > 0 {
		x++
	} else if y > 0 {
		y--
	} else {
		z += 1
	}
	for {
		break
	}
	for x < 10 {
		x *= 2
	}
	for i := 0; i < len(xs); i++ {
		if xs[i] == 0 {
			continue
		}
		total -= xs[i]
	}
	for ; x < 3; {
		x++
	}
	for i := range xs {
		total += i
	}
	for _, v := range xs {
		total += v
	}
	for k, v := range m {
		total += len(k) + v
	}
	for range xs {
		total <<= 1
	}
	var i, v int
	for i, v = range xs {
		total += i * v
	}
	switch policy := pick(); policy {
	case GradeNew, GradeUsed:
		total = 1
	case "other":
	default:
		total = 2
		return total
	}
	switch {
	case x > y:
		x, y = y, x
	}
	switch x {
	}
	return total
}
