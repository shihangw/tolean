// Package ledger is a small example for the Go translator: a double-entry
// journal entry, checked to balance and then posted line by line through a
// store interface, with errors and erased logging.
package ledger

import (
	"context"
	"errors"
	"fmt"
	"time"
)

var ErrUnbalanced = errors.New("ledger: entry does not balance")

type Side string

const (
	SideDebit  Side = "debit"
	SideCredit Side = "credit"
)

// Line is one line of a journal entry: an amount on one side of one account.
type Line struct {
	Account string
	Side    Side
	Amount  int64
}

type Log struct {
	Lines int
	Took  time.Duration
}

// Store holds the balances. Each method changes one account.
type Store interface {
	Debit(ctx context.Context, account string, n int64) (int64, error)
	Credit(ctx context.Context, account string, n int64) (int64, error)
}

// Post checks that the entry's debits equal its credits, and then applies
// each line. It returns the total that moved.
func Post(ctx context.Context, s Store, lines []Line, log *Log) (int64, error) {
	var debits, credits int64
	for i, l := range lines {
		if l.Amount <= 0 {
			return 0, fmt.Errorf("%w: line %d has amount %d", ErrUnbalanced, i, l.Amount)
		}
		switch l.Side {
		case SideDebit:
			debits += l.Amount
		case SideCredit:
			credits += l.Amount
		default:
			return 0, fmt.Errorf("%w: line %d has no side", ErrUnbalanced, i)
		}
	}
	if debits != credits || debits == 0 {
		return 0, fmt.Errorf("%w: debits %d, credits %d", ErrUnbalanced, debits, credits)
	}
	for _, l := range lines {
		start := time.Now()
		if l.Side == SideDebit {
			_, err := s.Debit(ctx, l.Account, l.Amount)
			if log != nil {
				log.Lines++
				log.Took += time.Since(start)
			}
			if err != nil {
				return 0, err
			}
			continue
		}
		if _, err := s.Credit(ctx, l.Account, l.Amount); err != nil {
			return 0, err
		}
	}
	return debits, nil
}
