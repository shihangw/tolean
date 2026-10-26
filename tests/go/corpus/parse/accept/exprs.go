package exprs

func g(order Order, items []Item) {
	if order.SKU == (SKU{}) || order.Qty < 0 && !order.Rush {
		return
	}
	for _, it := range items {
		_ = it
	}
	picks := make([]Pick, 0, len(items))
	picks = append(picks, Pick{SKU: order.SKU, Qty: -order.Qty, Bin: order.Bin})
	nested := [][]int{{1, 2}, {3}}
	points := map[string]Point{"a": {1, 2}, "b": {X: 3}}
	anon := struct {
		A int `json:"a"`
		B string
	}{A: 1, B: "x"}
	parts := []any{1, "two"}
	id := Make(parts...)
	ptr := &Stock{}
	val := *ptr
	half := id[:8]
	tail := id[8:]
	all := id[:]
	mid := id[2:4]
	bits := ^mask &^ other | x<<3>>1 ^ y%7
	f := float64(3.5e-2) + .5 + 1.
	r := 'x' + '\n' + '\''
	s := "quote \" and \\ and \t" + `raw
string`
	n := 0x1F + 0o17 + 0b101 + 1_000 + 017
	pkg.Value.Field.Call(1)(2)[3].X = n
	_, _, _, _, _, _, _, _, _, _, _, _ = picks, nested, points, anon, val, half, tail, all, mid, bits, f, r
	_ = s
}
