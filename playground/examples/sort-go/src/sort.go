package sorting

// Insert puts x into the sorted slice xs, before the first larger element.
func Insert(xs []int64, x int64) []int64 {
	out := []int64{}
	placed := false
	for _, y := range xs {
		if !placed && x <= y {
			out = append(out, x)
			placed = true
		}
		out = append(out, y)
	}
	if !placed {
		out = append(out, x)
	}
	return out
}

// Sort returns the elements of xs in ascending order.
func Sort(xs []int64) []int64 {
	out := []int64{}
	for _, x := range xs {
		out = Insert(out, x)
	}
	return out
}
