// Package fees computes the fee on a transfer. Most of its functions are
// pure, so Tolean translates them through the IR and proves that translation.
package fees

// Clamp keeps x between lo and hi.
func Clamp(x, lo, hi int64) int64 {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

// Fee is the fee on amount in basis points, with a minimum.
func Fee(amount int64, bps int64, minimum int64) int64 {
	fee := amount * bps
	var floor int64 = minimum
	if fee < floor {
		fee = floor
	}
	return fee
}

// Tier names the tier of an amount.
func Tier(amount int64) string {
	var name string
	if amount >= 1_000_000 {
		name = "large"
	} else if amount >= 0x2710 {
		name = "medium"
	} else {
		name = "small"
	}
	return name
}

// Steps counts how often start can drop by step, at most twice.
func Steps(start int, step int) int {
	n := start
	count := 0
	if n > step {
		n -= step
		count++
	}
	if n > step && count < 2 {
		n = n - step
		count += 1
	}
	return count
}

// Quote is the fee on amount, kept between 1 and 10000.
func Quote(amount int64, bps int64) int64 {
	return Clamp(Fee(amount, bps, 1), 1, 10_000)
}

// Label describes a transfer.
func Label(amount int64, express bool) string {
	label := Tier(amount)
	if express && !(amount < 0) {
		label += " express"
	}
	return label + "\n"
}

// Total adds the quotes for each amount. Its loop is outside the pure
// subset, so the older translation writes it.
func Total(amounts []int64, bps int64) int64 {
	var total int64
	for _, a := range amounts {
		total += Quote(a, bps)
	}
	return total
}
