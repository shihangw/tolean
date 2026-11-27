package named

// Celsius and Fahrenheit are temperatures. Go keeps them apart, and a
// conversion turns one into the other.
type Celsius int

type Fahrenheit int

const Boiling Celsius = 100

func ToFahrenheit(c Celsius) Fahrenheit {
	return Fahrenheit(c*9/5 + 32)
}

func Boils(c Celsius) bool {
	return c >= Boiling
}

type Open bool

func Closed(o Open) bool {
	var shut Open
	return o == shut
}
