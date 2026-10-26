// Package warehouse exercises top-level declarations.
package warehouse

import (
	"errors"
	"fmt"
	stdtime "time"
)

import "context"

type Grade string

const (
	GradeNew  Grade = "new"
	GradeUsed Grade = "used"
)

const MaxShelves = 5

var ErrMissing = errors.New("missing")

var (
	a, b int
	c    = 1
)

type SKU [16]byte

type Code = SKU

type Stock struct {
	Item    SKU
	Added   int64 `json:"added"`
	Removed int64
	Grade
	*stdtime.Location
	Tags       []string `json:"tags,omitempty"`
	Aisle, Bay string
	Spot       struct{ X, Y int }
	Index      map[string][]int
}

type Shelves interface {
	Find(ctx context.Context, item SKU) (Stock, error)
	Store(context.Context, Stock) error
	Count() int
	fmt.Stringer
}

type Sorter func(int, ...string) (n int, err error)
