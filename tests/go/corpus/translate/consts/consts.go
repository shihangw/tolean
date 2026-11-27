package consts

const Limit = 100

const (
	Fee     int64 = 3
	Prefix        = "id-"
	Enabled bool  = true
)

func Capped(n int) int {
	if n > Limit {
		return Limit
	}
	return n
}

func Charge(amount int64) int64 {
	if Enabled {
		return amount + Fee
	}
	return amount
}

func Label(name string) string {
	return Prefix + name
}

var fallback string

func NameOr(name string) string {
	if name == "" {
		return fallback
	}
	return name
}
