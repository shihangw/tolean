package funcs

func none() {}

func one(a int) int { return a }

func grouped(a, b int, c string, d ...any) (int, error) {
	return a + b, nil
}

func named() (n int, err error) {
	return
}

func unnamed(int, string) bool { return true }

func (s Stock) OnHand() int64 {
	return s.Added - s.Removed
}

func (s *Stock) Clear() {
	s.Removed = 0
}

func multiline(
	ctx Context,
	count int64,
	log *Logger,
) (
	Report,
	error,
) {
	return Report{}, nil
}
