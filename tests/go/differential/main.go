// Command differential checks the Go interpreter of tolean/Go/Spec/Eval.lean
// against Go itself, on random programs.
//
// Every claim of translate_sound holds relative to the interpreter, so the
// interpreter is trusted. This check is evidence that it means what Go means.
// It writes random pure functions of the proved subset, then runs each one
// with random arguments in three ways, and requires that all of them give the
// value that `go run` prints, or the same panic:
//
//   - the interpreter, Eval.runIn, on the functions as tolean parses them;
//   - the IR that Pure.translateFuncs produces, through IR.runIn;
//   - the Lean code that `tolean translate-go` prints, compiled by Lean.
//
// It also requires that Pure.translateFuncs accepts every generated function.
// A refusal means that the generator left the proved subset, or that the
// subset shrank, and both need a look.
//
// The generator covers the subset as docs/go/README.md describes it: int,
// int64, bool and string values; wrapping +, - and *; / and %, which panic on
// a zero divisor; the orders on integers; == and != on every type; &&, || and
// !; string concatenation; locals declared with := and var; =, +=, -=, *=,
// /=, %=, ++ and --; if statements that change locals or return; one counted
// loop at the start of a body; and calls of functions declared earlier. A
// function that may panic is called only where the subset allows it: alone
// after :=, =, var or return. Go's main recovers each panic and prints its
// message. When the subset grows, add the new construct here too.
//
// Run it from tests/go after `lake build`:
//
//	go run ./differential
//
// Set TOLEAN_SEED to repeat a run, and TOLEAN_PROGRAMS to run more programs.
// Set TOLEAN_KEEP=1 to keep the generated files. The check prints where they
// are.
package main

import (
	"fmt"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"time"
)

const tolean = "../../.lake/build/bin/tolean"

const callsPerFunction = 5

type ty int

const (
	tInt ty = iota
	tInt64
	tBool
	tString
)

var allTypes = []ty{tInt, tInt64, tBool, tString}

func (t ty) String() string {
	return [...]string{"int", "int64", "bool", "string"}[t]
}

func (t ty) isInt() bool { return t == tInt || t == tInt64 }

type local struct {
	name    string
	t       ty
	used    bool
	mutable bool
}

type fn struct {
	name   string
	params []ty
	result ty
	// The body divides, or calls a function that may panic, so a call of it
	// may panic.
	panics bool
}

type gen struct {
	r      *rand.Rand
	out    strings.Builder
	indent int
	// The functions of the current program that a body may call.
	callable []fn
	// The locals in scope, innermost last.
	locals []*local
	next   int
	// Inside a loop, a string assignment reads no string local and calls
	// nothing, so that a string cannot double on each iteration.
	inLoop, literalStrings bool
	// The function being written divides or calls a function that may panic.
	panics bool
	// The expression being written is the right operand of && or ||, where the
	// subset refuses a division.
	noDivide bool
}

func (g *gen) line(format string, args ...any) {
	g.out.WriteString(strings.Repeat("\t", g.indent))
	fmt.Fprintf(&g.out, format, args...)
	g.out.WriteString("\n")
}

func (g *gen) fresh() string {
	g.next++
	return fmt.Sprintf("v%d", g.next)
}

func (g *gen) pick(n int) int { return g.r.Intn(n) }

func (g *gen) chance(p float64) bool { return g.r.Float64() < p }

func (g *gen) visible(t ty, mutable bool) []*local {
	var out []*local
	for _, l := range g.locals {
		if l.t == t && (!mutable || l.mutable) {
			out = append(out, l)
		}
	}
	return out
}

var words = []string{"", "a", "ab", "Go", "xyz", "lean"}

func (g *gen) literal(t ty) string {
	switch t {
	case tBool:
		return [...]string{"true", "false"}[g.pick(2)]
	case tString:
		return strconv.Quote(words[g.pick(len(words))])
	default:
		return strconv.Itoa(g.pick(1001))
	}
}

// expr returns an expression of type t, and whether Go reads it as a
// constant. Two constant operands of an arithmetic operator would make Go
// fold them at compile time, where overflow is an error, so the generator
// never writes one.
func (g *gen) expr(t ty, depth int) (string, bool) {
	if t == tString && g.literalStrings {
		if depth > 0 && g.chance(0.3) {
			a, _ := g.expr(t, depth-1)
			b, _ := g.expr(t, depth-1)
			return "(" + a + " + " + b + ")", true
		}
		return g.literal(t), true
	}
	vars := g.visible(t, false)
	if depth <= 0 || g.chance(0.3) {
		if len(vars) > 0 && g.chance(0.7) {
			l := vars[g.pick(len(vars))]
			l.used = true
			return l.name, false
		}
		return g.literal(t), true
	}
	var calls []fn
	for _, f := range g.callable {
		if f.result == t {
			calls = append(calls, f)
		}
	}
	var safe []fn
	for _, f := range calls {
		if !f.panics {
			safe = append(safe, f)
		}
	}
	calls = safe
	if len(calls) > 0 && g.chance(0.15) {
		f := calls[g.pick(len(calls))]
		args := make([]string, len(f.params))
		for i, p := range f.params {
			args[i], _ = g.expr(p, depth-1)
		}
		return fmt.Sprintf("%s(%s)", f.name, strings.Join(args, ", ")), false
	}
	switch t {
	case tInt, tInt64:
		if g.chance(0.15) {
			a, c := g.expr(t, depth-1)
			return "-(" + a + ")", c
		}
		ops := []string{"+", "-", "*", "/", "%"}
		if g.noDivide {
			ops = ops[:3]
		}
		op := ops[g.pick(len(ops))]
		if op == "/" || op == "%" {
			return g.division(t, op, depth-1)
		}
		a, b, ok := g.intOperands(t, depth-1)
		if !ok {
			return a, true
		}
		return "(" + a + " " + op + " " + b + ")", false
	case tString:
		a, ca := g.expr(t, depth-1)
		b, cb := g.expr(t, depth-1)
		return "(" + a + " + " + b + ")", ca && cb
	default:
		switch g.pick(4) {
		case 0:
			a, c := g.expr(tBool, depth-1)
			return "!(" + a + ")", c
		case 1:
			op := []string{"&&", "||"}[g.pick(2)]
			a, ca := g.expr(tBool, depth-1)
			saved := g.noDivide
			g.noDivide = true
			b, cb := g.expr(tBool, depth-1)
			g.noDivide = saved
			return "(" + a + " " + op + " " + b + ")", ca && cb
		case 2:
			it := []ty{tInt, tInt64}[g.pick(2)]
			op := []string{"<", "<=", ">", ">=", "==", "!="}[g.pick(6)]
			a, b, ok := g.intOperands(it, depth-1)
			if !ok {
				return g.literal(tBool), true
			}
			return "(" + a + " " + op + " " + b + ")", false
		default:
			et := allTypes[g.pick(len(allTypes))]
			op := []string{"==", "!="}[g.pick(2)]
			if et.isInt() {
				a, b, ok := g.intOperands(et, depth-1)
				if !ok {
					return g.literal(tBool), true
				}
				return "(" + a + " " + op + " " + b + ")", false
			}
			a, ca := g.expr(et, depth-1)
			b, cb := g.expr(et, depth-1)
			return "(" + a + " " + op + " " + b + ")", ca && cb
		}
	}
}

// intOperands returns two operands of the integer type t for a binary
// operator. They are never both constants: Go would fold them at compile
// time, where overflow is an error, and the subset leaves out constant
// expressions. It reports false when it cannot avoid that, because no local
// of type t is in scope.
func (g *gen) intOperands(t ty, depth int) (string, string, bool) {
	a, ca := g.expr(t, depth)
	b, cb := g.expr(t, depth)
	if ca && cb {
		vars := g.visible(t, false)
		if len(vars) == 0 {
			return a, "", false
		}
		l := vars[g.pick(len(vars))]
		l.used = true
		b = l.name
	}
	return a, b, true
}

// division returns a / b or a % b on the integer type t. Go refuses a
// constant zero divisor, so a constant divisor becomes a nonzero literal, and
// two constant operands become a constant and a local.
func (g *gen) division(t ty, op string, depth int) (string, bool) {
	a, ca := g.expr(t, depth)
	b, cb := g.expr(t, depth)
	if cb {
		if ca {
			vars := g.visible(t, false)
			if len(vars) == 0 {
				return a, true
			}
			l := vars[g.pick(len(vars))]
			l.used = true
			b = l.name
		} else {
			// The translation tests no nonzero literal divisor, so the
			// division cannot panic.
			b = strconv.Itoa(1 + g.pick(9))
			return "(" + a + " " + op + " " + b + ")", false
		}
	}
	g.panics = true
	return "(" + a + " " + op + " " + b + ")", false
}

// panicking returns a call of a function of type t that may panic, and
// reports false when there is none. Inside a loop it calls none that returns
// a string, so that a string cannot double on each iteration.
func (g *gen) panicking(t ty) (string, bool) {
	var fs []fn
	for _, f := range g.callable {
		if f.panics && f.result == t && !(g.inLoop && t == tString) {
			fs = append(fs, f)
		}
	}
	if len(fs) == 0 {
		return "", false
	}
	f := fs[g.pick(len(fs))]
	args := make([]string, len(f.params))
	for i, p := range f.params {
		g.literalStrings = g.inLoop && p == tString
		args[i], _ = g.expr(p, 1)
		g.literalStrings = false
	}
	g.panics = true
	return fmt.Sprintf("%s(%s)", f.name, strings.Join(args, ", ")), true
}

// nonConst returns an expression of type t that Go does not read as a
// constant, so that `x := e` gives x the type t.
func (g *gen) nonConst(t ty, depth int) (string, bool) {
	for range 8 {
		if e, c := g.expr(t, depth); !c {
			return e, true
		}
	}
	return "", false
}

func (g *gen) declare(t ty) *local {
	l := &local{name: g.fresh(), t: t, mutable: true}
	g.locals = append(g.locals, l)
	return l
}

// use reads every local declared since mark that nothing read, because Go
// refuses a local that is never used. The `if` changes the local, so that the
// subset accepts it.
func (g *gen) use(mark int) {
	for _, l := range g.locals[mark:] {
		if l.used {
			continue
		}
		l.used = true
		switch l.t {
		case tBool:
			g.line("if %s {", l.name)
			g.line("\t%s = false", l.name)
		case tString:
			g.line("if %s == \"a\" {", l.name)
			g.line("\t%s = \"\"", l.name)
		default:
			g.line("if %s > 0 {", l.name)
			g.line("\t%s = 0", l.name)
		}
		g.line("}")
	}
}

// assign writes a statement that changes a local declared before mark, so
// that an if that does not return changes some local, as the subset
// requires. It reports false when there is no such local.
func (g *gen) assign(mark int) bool {
	var outer []*local
	for _, l := range g.locals[:mark] {
		if l.mutable {
			outer = append(outer, l)
		}
	}
	if len(outer) == 0 {
		return false
	}
	l := outer[g.pick(len(outer))]
	if l.t.isInt() && g.chance(0.3) {
		g.line("%s%s", l.name, []string{"++", "--"}[g.pick(2)])
		return true
	}
	if g.chance(0.15) {
		if e, ok := g.panicking(l.t); ok {
			g.line("%s = %s", l.name, e)
			return true
		}
	}
	g.literalStrings = g.inLoop && l.t == tString
	e, ce := g.expr(l.t, 2)
	g.literalStrings = false
	switch {
	case l.t.isInt() && g.chance(0.2):
		// Go refuses a constant zero divisor.
		if ce {
			e = strconv.Itoa(1 + g.pick(9))
		} else {
			g.panics = true
		}
		g.line("%s %s %s", l.name, []string{"/=", "%="}[g.pick(2)], e)
	case l.t.isInt() && g.chance(0.5):
		g.line("%s %s %s", l.name, []string{"+=", "-=", "*="}[g.pick(3)], e)
	case l.t == tString && g.chance(0.5):
		g.line("%s += %s", l.name, e)
	default:
		g.line("%s = %s", l.name, e)
	}
	return true
}

// stmts writes up to n statements that do not return.
func (g *gen) stmts(n, depth int) {
	for range n {
		switch g.pick(5) {
		case 0, 1:
			t := allTypes[g.pick(len(allTypes))]
			if g.chance(0.2) {
				if e, ok := g.panicking(t); ok {
					l := g.declare(t)
					if g.chance(0.5) {
						g.line("%s := %s", l.name, e)
					} else {
						g.line("var %s %s = %s", l.name, t, e)
					}
					continue
				}
			}
			if g.chance(0.5) {
				if e, ok := g.nonConst(t, 2); ok {
					g.declare(t)
					g.line("%s := %s", g.locals[len(g.locals)-1].name, e)
					continue
				}
			}
			if g.chance(0.3) {
				l := g.declare(t)
				g.line("var %s %s", l.name, t)
			} else {
				e, _ := g.expr(t, 2)
				l := g.declare(t)
				g.line("var %s %s = %s", l.name, t, e)
			}
		case 2, 3:
			g.assign(len(g.locals))
		default:
			if depth > 0 {
				g.stateIf(depth - 1)
			}
		}
	}
}

// block writes `{ … }` whose statements change a local declared before it.
func (g *gen) stateBlock(depth int) {
	mark := len(g.locals)
	g.indent++
	g.stmts(g.pick(3), depth)
	g.assign(mark)
	g.use(mark)
	g.indent--
	g.locals = g.locals[:mark]
}

// stateIf writes an if that does not return.
func (g *gen) stateIf(depth int) {
	if len(g.visible(tInt, true))+len(g.visible(tInt64, true))+
		len(g.visible(tBool, true))+len(g.visible(tString, true)) == 0 {
		return
	}
	c, _ := g.expr(tBool, 2)
	g.line("if %s {", c)
	g.stateBlock(depth)
	if g.chance(0.5) {
		g.line("} else {")
		g.stateBlock(depth)
	}
	g.line("}")
}

// returning writes statements that end with a return of type t.
func (g *gen) returning(t ty, depth int) {
	mark := len(g.locals)
	g.stmts(g.pick(4), depth)
	switch {
	case depth > 0 && g.chance(0.3):
		g.use(mark)
		c, _ := g.expr(tBool, 2)
		g.line("if %s {", c)
		g.indent++
		g.returning(t, depth-1)
		g.indent--
		g.line("}")
		g.returning(t, depth-1)
	case depth > 0 && g.chance(0.3):
		g.use(mark)
		c, _ := g.expr(tBool, 2)
		g.line("if %s {", c)
		g.indent++
		g.returning(t, depth-1)
		g.indent--
		g.line("} else {")
		g.indent++
		g.returning(t, depth-1)
		g.indent--
		g.line("}")
	default:
		e, ok := "", false
		if g.chance(0.2) {
			e, ok = g.panicking(t)
		}
		if !ok {
			e, _ = g.expr(t, 3)
		}
		g.use(mark)
		g.line("return %s", e)
	}
	g.locals = g.locals[:mark]
}

// loop writes the counted loop that may start a body: literal bounds that
// give at most 256 iterations, and a body that changes a parameter.
func (g *gen) loop() {
	start := g.pick(20)
	stop := start + g.pick(40)
	if g.chance(0.1) {
		stop = start + 256
	}
	if g.chance(0.05) {
		// An empty loop. Its bound must be a literal, which is never
		// negative.
		start++
		stop = start - 1
	}
	index := &local{name: g.fresh(), t: tInt}
	g.line("for %s := %d; %s < %d; %s++ {", index.name, start, index.name, stop, index.name)
	mark := len(g.locals)
	g.locals = append(g.locals, index)
	g.inLoop = true
	g.indent++
	g.stmts(g.pick(3), 1)
	g.assign(mark)
	g.use(mark + 1)
	g.inLoop = false
	g.indent--
	g.locals = g.locals[:mark]
	g.line("}")
}

func (g *gen) function(f *fn) {
	g.locals = nil
	g.panics = false
	params := make([]string, len(f.params))
	for i, p := range f.params {
		l := &local{name: fmt.Sprintf("p%d", i), t: p, mutable: true}
		g.locals = append(g.locals, l)
		params[i] = l.name + " " + p.String()
	}
	g.line("func %s(%s) %s {", f.name, strings.Join(params, ", "), f.result)
	g.indent++
	if len(params) > 0 && g.chance(0.3) {
		g.loop()
	}
	g.returning(f.result, 2)
	g.indent--
	g.line("}")
	g.line("")
	f.panics = g.panics
}

func (g *gen) value(t ty) (goText, leanVal, leanArg string) {
	switch t {
	case tBool:
		b := []string{"true", "false"}[g.pick(2)]
		return b, "(.bool " + b + ")", b
	case tString:
		s := strconv.Quote(words[g.pick(len(words))])
		return s, "(.str " + s + ")", s
	}
	var n int64
	switch g.pick(4) {
	case 0:
		n = int64(g.pick(11) - 5)
	case 1:
		n = []int64{math.MaxInt64, math.MinInt64, math.MaxInt64 - 1, math.MinInt64 + 1}[g.pick(4)]
	case 2:
		n = int64(g.r.Uint64())
	default:
		n = int64(g.pick(2001) - 1000)
	}
	s := strconv.FormatInt(n, 10)
	return s, "(.int (" + s + "))", "(" + s + " : Int)"
}

type call struct {
	fn               string
	goArgs, leanVals []string
	leanArgs         []string
	result           ty
	// The translation returns an Except.
	panics bool
}

// chunks defines name as a list of items. It writes the list in parts of 50,
// because Lean's elaborator and code generator run out of recursion depth on
// one long list literal.
func chunks(l *strings.Builder, name, elem string, items []string) {
	var parts []string
	for i := 0; i < len(items); i += 50 {
		part := fmt.Sprintf("%s%d", name, len(parts))
		parts = append(parts, part)
		fmt.Fprintf(l, "def %s : List %s := [\n%s]\n\n", part, elem, strings.Join(items[i:min(i+50, len(items))], ",\n"))
	}
	if len(parts) == 0 {
		parts = []string{"[]"}
	}
	fmt.Fprintf(l, "def %s : List %s := %s\n\n", name, elem, strings.Join(parts, " ++ "))
}

func leanString(s string) string {
	r := strings.NewReplacer(`\`, `\\`, `"`, `\"`, "\n", `\n`, "\t", `\t`)
	return `"` + r.Replace(s) + `"`
}

func run(dir, name string, args ...string) (string, error) {
	cmd := exec.Command(name, args...)
	cmd.Dir = dir
	out, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("%s %s: %v\n%s", name, strings.Join(args, " "), err, out)
	}
	return string(out), nil
}

func main() {
	seed := time.Now().UnixNano() % 1_000_000_000
	if s := os.Getenv("TOLEAN_SEED"); s != "" {
		seed, _ = strconv.ParseInt(s, 10, 64)
	}
	programs := 100
	if s := os.Getenv("TOLEAN_PROGRAMS"); s != "" {
		programs, _ = strconv.Atoi(s)
	}
	fmt.Printf("differential: seed %d, %d programs\n", seed, programs)
	if err := check(seed, programs); err != nil {
		fmt.Printf("FAIL (TOLEAN_SEED=%d): %v\n", seed, err)
		os.Exit(1)
	}
}

func check(seed int64, programs int) error {
	root, err := filepath.Abs("../..")
	if err != nil {
		return err
	}
	toleanPath, err := filepath.Abs(tolean)
	if err != nil {
		return err
	}
	dir, err := os.MkdirTemp("", "tolean-differential-")
	if err != nil {
		return err
	}
	if os.Getenv("TOLEAN_KEEP") != "" {
		fmt.Printf("differential: files in %s\n", dir)
	} else {
		defer os.RemoveAll(dir)
	}

	g := &gen{r: rand.New(rand.NewSource(seed))}
	g.line("package main")
	g.line("")
	var order []string
	var calls []call
	for p := range programs {
		g.callable = nil
		for j := range 1 + g.pick(4) {
			f := fn{name: fmt.Sprintf("P%dF%d", p, j), result: allTypes[g.pick(len(allTypes))]}
			for range g.pick(4) {
				f.params = append(f.params, allTypes[g.pick(len(allTypes))])
			}
			g.function(&f)
			g.callable = append(g.callable, f)
			order = append(order, f.name)
			for range callsPerFunction {
				c := call{fn: f.name, result: f.result, panics: f.panics}
				for _, t := range f.params {
					a, v, l := g.value(t)
					c.goArgs = append(c.goArgs, a)
					c.leanVals = append(c.leanVals, v)
					c.leanArgs = append(c.leanArgs, l)
				}
				calls = append(calls, c)
			}
		}
	}
	source := g.out.String()
	if err := os.WriteFile(filepath.Join(dir, "gen.go"), []byte(source), 0o644); err != nil {
		return err
	}

	// Go: a main that prints each result on its own line.
	var m strings.Builder
	// show recovers a panic and prints its message.
	m.WriteString("package main\n\nimport \"fmt\"\n\n")
	m.WriteString("func show(f func() string) (s string) {\n\tdefer func() {\n" +
		"\t\tif r := recover(); r != nil {\n\t\t\ts = fmt.Sprint(\"panic: \", r)\n\t\t}\n\t}()\n" +
		"\treturn f()\n}\n\nfunc main() {\n")
	for _, c := range calls {
		format := "%d"
		switch c.result {
		case tBool:
			format = "%t"
		case tString:
			format = "%q"
		}
		fmt.Fprintf(&m, "\tfmt.Println(show(func() string { return fmt.Sprintf(%q, %s(%s)) }))\n",
			format, c.fn, strings.Join(c.goArgs, ", "))
	}
	m.WriteString("}\n")
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(m.String()), 0o644); err != nil {
		return err
	}
	goOut, err := run(dir, "go", "run", "gen.go", "main.go")
	if err != nil {
		return err
	}
	results := strings.Split(strings.TrimSuffix(goOut, "\n"), "\n")
	if len(results) != len(calls) {
		return fmt.Errorf("go run printed %d results for %d calls", len(results), len(calls))
	}

	// The translation that `tolean translate-go` prints.
	translated := filepath.Join(dir, "Diff.lean")
	translateArgs := []string{"translate-go"}
	for _, n := range order {
		translateArgs = append(translateArgs, "--root", n)
	}
	translateArgs = append(translateArgs, translated, "Diff", "gen.go")
	if _, err := run(dir, toleanPath, translateArgs...); err != nil {
		return err
	}
	text, err := os.ReadFile(translated)
	if err != nil {
		return err
	}
	body := strings.Replace(string(text), "import tolean.Go.Spec.Basic\n", "", 1)

	// Lean: the translation, then one #eval that parses gen.go once and runs
	// every call in the interpreter and in the IR, and one that runs every
	// call of the translation. Each prints every disagreement and fails.
	var l strings.Builder
	l.WriteString("import tolean.Go.Spec.Basic\nimport tolean.Go.Syntax.Parser\nimport tolean.Go.Proof.Package\n")
	l.WriteString(body)
	l.WriteString("\nopen tolean.Go\n\n")
	fmt.Fprintf(&l, "def source : String := %s\n\n", leanString(source))
	quoted := make([]string, len(order))
	for i, n := range order {
		quoted[i] = strconv.Quote(n)
	}
	fmt.Fprintf(&l, "def order : List String := [%s]\n\n", strings.Join(quoted, ", "))
	var vals, translatedChecks []string
	for i, c := range calls {
		var leanResult, leanVal string
		label := fmt.Sprintf("%s(%s) = %s", c.fn, strings.Join(c.goArgs, ", "), results[i])
		leanCall := fmt.Sprintf("Diff.%s %s", c.fn, strings.Join(c.leanArgs, " "))
		if msg, ok := strings.CutPrefix(results[i], "panic: "); ok {
			if !c.panics {
				return fmt.Errorf("%s panics, but the generator wrote no division or call that may panic", label)
			}
			vals = append(vals, fmt.Sprintf("  (%q, [%s], .error (.str %s))", c.fn, strings.Join(c.leanVals, ", "), leanString(msg)))
			translatedChecks = append(translatedChecks, fmt.Sprintf("  (%s, match %s with | .error e => e == %s | .ok _ => false)",
				leanString(label), leanCall, leanString(msg)))
			continue
		}
		switch c.result {
		case tBool:
			leanResult, leanVal = results[i], "(.bool "+results[i]+")"
		case tString:
			s, err := strconv.Unquote(results[i])
			if err != nil {
				return fmt.Errorf("go run printed %q", results[i])
			}
			leanResult = leanString(s)
			leanVal = "(.str " + leanResult + ")"
		default:
			leanResult = "(" + results[i] + " : Int)"
			leanVal = "(.int (" + results[i] + "))"
		}
		vals = append(vals, fmt.Sprintf("  (%q, [%s], .ok %s)", c.fn, strings.Join(c.leanVals, ", "), leanVal))
		check := fmt.Sprintf("%s == %s", leanCall, leanResult)
		if c.panics {
			check = fmt.Sprintf("match %s with | .ok v => v == %s | .error _ => false", leanCall, leanResult)
		}
		translatedChecks = append(translatedChecks, fmt.Sprintf("  (%s, %s)", leanString(label), check))
	}
	chunks(&l, "calls", "(String × List Eval.Val × Except Eval.Val Eval.Val)", vals)
	l.WriteString(`#eval show IO Unit from do
  let decls ← match Syntax.parse source with
    | .ok file => pure file.decls
    | .error _ => throw (IO.userError "tolean cannot parse gen.go")
  let out := Pure.translateFuncs decls order
  let known := out.map (·.2)
  -- The reason for each refusal, as gen.go:LINE:COL: REASON, so that a
  -- generator bug shows where it is.
  let refusals := order.filterMap fun n =>
    match Pure.findFunc decls n with
    | none => some s!"{n}: not found"
    | some d => match Pure.translateFunc ⟨Eval.program decls, known⟩ d with
      | .ok _ => if known.any (·.name == n) then none else some s!"{n}: calls a refused function"
      | .error e => some s!"{n}: gen.go:{e}"
  unless refusals.isEmpty do
    throw (IO.userError ("the proved path refuses generated functions:\n" ++ "\n".intercalate refusals))
  let program := Eval.program decls
  let fs := IR.functions (out.map (·.1))
  -- The value that a call returns, or the panic, as text: Except has no
  -- BEq instance.
  let text : Option (Except Eval.Val Eval.Val) → String
    | some (.ok v) => s!"value {repr v}"
    | some (.error v) => s!"panic {repr v}"
    | none => "no result"
  let mut bad : Array String := #[]
  for (f, args, want) in calls do
    let want := text (some want)
    let got := text (Eval.runIn program f args)
    if got != want then
      bad := bad.push s!"interpreter: {f} {repr args} gives {got}, Go gives {want}"
    let got := text (IR.runIn fs ⟨"", f⟩ args)
    if got != want then
      bad := bad.push s!"IR: {f} {repr args} gives {repr got}, Go gives {repr want}"
  unless bad.isEmpty do
    throw (IO.userError ("\n".intercalate bad.toList))

`)
	chunks(&l, "translated", "(String × Bool)", translatedChecks)
	l.WriteString(`#eval show IO Unit from do
  let bad := translated.filter (!·.2)
  unless bad.isEmpty do
    throw (IO.userError ("the translation disagrees with Go:\n" ++ "\n".intercalate (bad.map (·.1))))
`)
	check := filepath.Join(dir, "Check.lean")
	if err := os.WriteFile(check, []byte(l.String()), 0o644); err != nil {
		return err
	}
	if _, err := run(root, "lake", "env", "lean", check); err != nil {
		return err
	}
	fmt.Printf("differential: %d functions and %d calls agree with go run\n", len(order), len(calls))
	return nil
}
