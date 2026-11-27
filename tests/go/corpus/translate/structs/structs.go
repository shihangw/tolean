package structs

type Point struct {
	X int
	Y int
}

type Account struct {
	Owner   string
	Balance int64
	Open    bool
}

func Origin() Point {
	return Point{}
}

func Sum(x int, y int) int {
	p := Point{x, y}
	return p.X + p.Y
}

func Deposit(owner string, amount int64) int64 {
	a := Account{Owner: owner, Balance: 0, Open: true}
	if a.Open {
		a.Balance = a.Balance + amount
	}
	return a.Balance
}
