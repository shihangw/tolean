package lexer // trailing comment

/* a block comment */

func h() (int, int) { /* one line */
	a := 1 /* a comment
	that spans lines ends the statement */
	b := a +
		2
	c := []int{
		1,
		2,
	}
	return c[0], b // done
}
