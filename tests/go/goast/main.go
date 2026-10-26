// Command goast prints the syntax tree that go/parser gives for a Go file, in
// the S-expression form of tolean/Sexp.lean. The Lean parser in
// tolean/Go/Syntax prints the same form, and tests/go/check compares the two.
//
// It refuses the node kinds that the Lean parser does not read, so that a
// refusal on both sides counts as agreement.
//
// Spans are line:col-line:col. Columns count Unicode code points, as tolean's
// spans do, not bytes as go/token does.
//
//	go run ./goast file.go
package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"strings"
	"unicode/utf8"
)

// refusal is a node kind that the Lean parser does not read.
type refusal struct{ what string }

type printer struct {
	fset  *token.FileSet
	lines [][]byte // source lines, for code-point columns
	out   strings.Builder
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: goast file.go")
		os.Exit(2)
	}
	path := os.Args[1]
	src, err := os.ReadFile(path)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, path, src, parser.SkipObjectResolution)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	p := &printer{fset: fset, lines: splitLines(src)}
	defer func() {
		if r := recover(); r != nil {
			if ref, ok := r.(refusal); ok {
				fmt.Fprintf(os.Stderr, "refused: %s\n", ref.what)
				os.Exit(3)
			}
			panic(r)
		}
	}()
	p.file(file)
	fmt.Print(p.out.String())
	fmt.Println()
}

func splitLines(src []byte) [][]byte {
	var lines [][]byte
	start := 0
	for i, b := range src {
		if b == '\n' {
			lines = append(lines, src[start:i])
			start = i + 1
		}
	}
	return append(lines, src[start:])
}

func refuse(format string, args ...any) {
	panic(refusal{fmt.Sprintf(format, args...)})
}

// pos renders a go/token position as line:col with a code-point column.
func (p *printer) pos(pos token.Pos) string {
	position := p.fset.Position(pos)
	line := p.lines[position.Line-1]
	col := utf8.RuneCount(line[:position.Column-1]) + 1
	return fmt.Sprintf("%d:%d", position.Line, col)
}

func (p *printer) span(n ast.Node) string {
	return p.pos(n.Pos()) + "-" + p.pos(n.End())
}

// quote writes s as JSON.stringify does, like Sexp.quote in Lean.
func quote(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString(`\"`)
		case '\\':
			b.WriteString(`\\`)
		case '\n':
			b.WriteString(`\n`)
		case '\r':
			b.WriteString(`\r`)
		case '\t':
			b.WriteString(`\t`)
		case 0x08:
			b.WriteString(`\b`)
		case 0x0C:
			b.WriteString(`\f`)
		default:
			if r < 0x20 {
				fmt.Fprintf(&b, `\u%04x`, r)
			} else {
				b.WriteRune(r)
			}
		}
	}
	b.WriteByte('"')
	return b.String()
}

// sexp is one node: a head, an optional span, atoms and children.
type sexp struct {
	head     string
	span     string
	atoms    []string
	children []sexp
}

func (s sexp) render(indent int) string {
	parts := []string{s.head}
	if s.span != "" {
		parts = append(parts, s.span)
	}
	parts = append(parts, s.atoms...)
	var b strings.Builder
	b.WriteString("(" + strings.Join(parts, " "))
	for _, c := range s.children {
		b.WriteString("\n" + strings.Repeat(" ", indent+2) + c.render(indent+2))
	}
	b.WriteString(")")
	return b.String()
}

func (p *printer) node(head string, n ast.Node, atoms []string, children ...sexp) sexp {
	return sexp{head: head, span: p.span(n), atoms: atoms, children: children}
}

// group is a node without a span that names a part of its parent, such as
// the init statement of an `if`.
func group(head string, children ...sexp) sexp {
	return sexp{head: head, children: children}
}

func (p *printer) file(f *ast.File) {
	var decls []sexp
	for _, d := range f.Decls {
		decls = append(decls, p.decl(d))
	}
	root := sexp{head: "file", atoms: []string{f.Name.Name}, children: decls}
	p.out.WriteString(root.render(0))
}

func (p *printer) decl(d ast.Decl) sexp {
	switch d := d.(type) {
	case *ast.FuncDecl:
		if d.Type.TypeParams != nil {
			refuse("type parameters")
		}
		if d.Body == nil {
			refuse("a function without a body")
		}
		var children []sexp
		if d.Recv != nil {
			children = append(children, group("recv", p.fields(d.Recv)...))
		}
		children = append(children, p.signature(d.Type)...)
		children = append(children, p.stmt(d.Body))
		return p.node("func", d, []string{d.Name.Name}, children...)
	case *ast.GenDecl:
		var specs []sexp
		for _, s := range d.Specs {
			specs = append(specs, p.spec(s))
		}
		return p.node("decl-"+d.Tok.String(), d, nil, specs...)
	default:
		refuse("declaration %T", d)
		return sexp{}
	}
}

func (p *printer) spec(s ast.Spec) sexp {
	switch s := s.(type) {
	case *ast.ImportSpec:
		atoms := []string{quote(s.Path.Value)}
		if s.Name != nil {
			atoms = append(atoms, s.Name.Name)
		}
		return p.node("import-spec", s, atoms)
	case *ast.TypeSpec:
		if s.TypeParams != nil {
			refuse("type parameters")
		}
		if s.Assign.IsValid() {
			return p.node("alias-spec", s, []string{s.Name.Name}, p.expr(s.Type))
		}
		return p.node("type-spec", s, []string{s.Name.Name}, p.expr(s.Type))
	case *ast.ValueSpec:
		var names []string
		for _, n := range s.Names {
			names = append(names, n.Name)
		}
		var children []sexp
		if s.Type != nil {
			children = append(children, group("type", p.expr(s.Type)))
		}
		if len(s.Values) > 0 {
			children = append(children, group("values", p.exprs(s.Values)...))
		}
		return p.node("value-spec", s, names, children...)
	default:
		refuse("spec %T", s)
		return sexp{}
	}
}

func (p *printer) signature(t *ast.FuncType) []sexp {
	out := []sexp{group("params", p.fields(t.Params)...)}
	if t.Results != nil {
		out = append(out, group("results", p.fields(t.Results)...))
	}
	return out
}

func (p *printer) fields(list *ast.FieldList) []sexp {
	if list == nil {
		return nil
	}
	var out []sexp
	for _, f := range list.List {
		var names []string
		for _, n := range f.Names {
			names = append(names, n.Name)
		}
		children := []sexp{p.expr(f.Type)}
		if f.Tag != nil {
			children = append(children, p.expr(f.Tag))
		}
		out = append(out, p.node("field", f, names, children...))
	}
	return out
}

func (p *printer) exprs(list []ast.Expr) []sexp {
	var out []sexp
	for _, e := range list {
		out = append(out, p.expr(e))
	}
	return out
}

func (p *printer) stmts(list []ast.Stmt) []sexp {
	var out []sexp
	for _, s := range list {
		out = append(out, p.stmt(s))
	}
	return out
}

func (p *printer) expr(e ast.Expr) sexp {
	switch e := e.(type) {
	case *ast.Ident:
		return p.node("ident", e, []string{e.Name})
	case *ast.BasicLit:
		if e.Kind == token.IMAG {
			refuse("imaginary literals")
		}
		return p.node("lit", e, []string{e.Kind.String(), quote(e.Value)})
	case *ast.CompositeLit:
		var children []sexp
		if e.Type != nil {
			children = append(children, group("type", p.expr(e.Type)))
		}
		children = append(children, p.exprs(e.Elts)...)
		return p.node("composite", e, nil, children...)
	case *ast.KeyValueExpr:
		return p.node("key-value", e, nil, p.expr(e.Key), p.expr(e.Value))
	case *ast.ParenExpr:
		return p.node("paren", e, nil, p.expr(e.X))
	case *ast.SelectorExpr:
		return p.node("selector", e, []string{e.Sel.Name}, p.expr(e.X))
	case *ast.IndexExpr:
		return p.node("index", e, nil, p.expr(e.X), p.expr(e.Index))
	case *ast.SliceExpr:
		if e.Slice3 {
			refuse("three-index slices")
		}
		children := []sexp{p.expr(e.X)}
		if e.Low != nil {
			children = append(children, group("low", p.expr(e.Low)))
		}
		if e.High != nil {
			children = append(children, group("high", p.expr(e.High)))
		}
		return p.node("slice-expr", e, nil, children...)
	case *ast.CallExpr:
		var atoms []string
		if e.Ellipsis.IsValid() {
			atoms = []string{"..."}
		}
		return p.node("call", e, atoms, append([]sexp{p.expr(e.Fun)}, p.exprs(e.Args)...)...)
	case *ast.StarExpr:
		return p.node("star", e, nil, p.expr(e.X))
	case *ast.UnaryExpr:
		return p.node("unary", e, []string{e.Op.String()}, p.expr(e.X))
	case *ast.BinaryExpr:
		return p.node("binary", e, []string{e.Op.String()}, p.expr(e.X), p.expr(e.Y))
	case *ast.ArrayType:
		if e.Len == nil {
			return p.node("slice-type", e, nil, p.expr(e.Elt))
		}
		if _, ok := e.Len.(*ast.Ellipsis); ok {
			refuse("[...]T array types")
		}
		return p.node("array-type", e, nil, p.expr(e.Len), p.expr(e.Elt))
	case *ast.MapType:
		return p.node("map-type", e, nil, p.expr(e.Key), p.expr(e.Value))
	case *ast.StructType:
		return p.node("struct-type", e, nil, p.fields(e.Fields)...)
	case *ast.InterfaceType:
		return p.node("interface-type", e, nil, p.fields(e.Methods)...)
	case *ast.FuncType:
		if e.TypeParams != nil {
			refuse("type parameters")
		}
		return p.node("func-type", e, nil, p.signature(e)...)
	case *ast.Ellipsis:
		return p.node("ellipsis", e, nil, p.expr(e.Elt))
	case *ast.TypeAssertExpr:
		children := []sexp{p.expr(e.X)}
		if e.Type != nil {
			children = append(children, p.expr(e.Type))
		}
		return p.node("type-assert", e, nil, children...)
	case *ast.FuncLit:
		return p.node("func-lit", e, nil, p.expr(e.Type), p.stmt(e.Body))
	default:
		refuse("expression %T", e)
		return sexp{}
	}
}

func (p *printer) stmt(s ast.Stmt) sexp {
	switch s := s.(type) {
	case *ast.BlockStmt:
		return p.node("block", s, nil, p.stmts(s.List)...)
	case *ast.ExprStmt:
		return p.node("expr", s, nil, p.expr(s.X))
	case *ast.AssignStmt:
		return p.node("assign", s, []string{s.Tok.String()},
			group("lhs", p.exprs(s.Lhs)...), group("rhs", p.exprs(s.Rhs)...))
	case *ast.IncDecStmt:
		return p.node("inc-dec", s, []string{s.Tok.String()}, p.expr(s.X))
	case *ast.DeclStmt:
		return p.node("decl-stmt", s, nil, p.decl(s.Decl))
	case *ast.ReturnStmt:
		return p.node("return", s, nil, p.exprs(s.Results)...)
	case *ast.BranchStmt:
		if s.Label != nil {
			refuse("labels")
		}
		if s.Tok != token.BREAK && s.Tok != token.CONTINUE {
			refuse("%s", s.Tok)
		}
		return p.node(s.Tok.String(), s, nil)
	case *ast.IfStmt:
		var children []sexp
		if s.Init != nil {
			children = append(children, group("init", p.stmt(s.Init)))
		}
		children = append(children, p.expr(s.Cond), p.stmt(s.Body))
		if s.Else != nil {
			children = append(children, group("else", p.stmt(s.Else)))
		}
		return p.node("if", s, nil, children...)
	case *ast.ForStmt:
		var children []sexp
		if s.Init != nil {
			children = append(children, group("init", p.stmt(s.Init)))
		}
		if s.Cond != nil {
			children = append(children, group("cond", p.expr(s.Cond)))
		}
		if s.Post != nil {
			children = append(children, group("post", p.stmt(s.Post)))
		}
		children = append(children, p.stmt(s.Body))
		return p.node("for", s, nil, children...)
	case *ast.RangeStmt:
		var atoms []string
		if s.Tok != token.ILLEGAL {
			atoms = []string{s.Tok.String()}
		}
		var children []sexp
		if s.Key != nil {
			children = append(children, group("key", p.expr(s.Key)))
		}
		if s.Value != nil {
			children = append(children, group("value", p.expr(s.Value)))
		}
		children = append(children, p.expr(s.X), p.stmt(s.Body))
		return p.node("range", s, atoms, children...)
	case *ast.DeferStmt:
		return p.node("defer", s, nil, p.expr(s.Call))
	case *ast.TypeSwitchStmt:
		var children []sexp
		if s.Init != nil {
			children = append(children, group("init", p.stmt(s.Init)))
		}
		children = append(children, group("assign", p.stmt(s.Assign)))
		children = append(children, p.caseBlock(s.Body))
		return p.node("type-switch", s, nil, children...)
	case *ast.SwitchStmt:
		var children []sexp
		if s.Init != nil {
			children = append(children, group("init", p.stmt(s.Init)))
		}
		if s.Tag != nil {
			children = append(children, group("tag", p.expr(s.Tag)))
		}
		children = append(children, p.caseBlock(s.Body))
		return p.node("switch", s, nil, children...)
	default:
		refuse("statement %T", s)
		return sexp{}
	}
}

// caseBlock prints the body of a switch or a type switch.
func (p *printer) caseBlock(body *ast.BlockStmt) sexp {
	var clauses []sexp
	for _, c := range body.List {
		cc := c.(*ast.CaseClause)
		var atoms []string
		if cc.List == nil {
			atoms = []string{"default"}
		}
		clauses = append(clauses, p.node("case", cc, atoms,
			append([]sexp{group("exprs", p.exprs(cc.List)...)}, p.stmts(cc.Body)...)...))
	}
	return p.node("block", body, nil, clauses...)
}
