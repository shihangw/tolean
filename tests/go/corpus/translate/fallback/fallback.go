// Package fallback holds pure functions that the proved path refuses, so
// that the older string translation writes them, as it did before. Each
// caller then calls them the way that translation declares them.
package fallback

// Ignore has a parameter without a name, which still takes an argument.
func Ignore(int) int { return 7 }

// partial is a Lean keyword, so the output must quote it.
func partial(x int) int { return x }

// Caller calls both.
func Caller() int { return Ignore(42) + partial(1) }
