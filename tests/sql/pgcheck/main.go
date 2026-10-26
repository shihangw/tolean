// Command pgcheck checks tolean's SQL translator against a real PostgreSQL.
//
//	go run ./pgcheck schema [--keep-going] --table T... --migrations FILE...
//
// starts a throwaway cluster, applies the migrations in order, and prints the
// schema of the tables T (and the tables their foreign keys point to) from the
// catalog, in the form `tolean sql-schema` prints. With --keep-going, a
// failing statement is reported and skipped, for migrations that need
// extensions the local server lacks.
//
//	go run ./pgcheck scenarios [--keep-going] --migrations FILE... --queries FILE... --scenarios FILE
//
//	go run ./pgcheck corpus
//
// runs every check for each directory in corpus/: the translation equals the
// committed .lean file and Lean compiles it, the schema matches the catalog,
// and the scenarios that the directory's Scenarios.lean writes agree with
// PostgreSQL. The `args` file holds the namespace and the --query options on
// its first line and the --table options on its second.
//
// The corpus command also checks each directory in reject/: tolean must refuse
// to translate it, with the message in its `expect` file. And it checks the
// READ COMMITTED behavior that tolean's concurrency model relies on (see
// checkIsolation).
//
// The scenarios command applies the migrations, then runs each scenario in the JSON-lines file in a
// transaction that it rolls back: the setup statements, the named sqlc query
// with its arguments substituted, and a statement that prints the tables. The
// output must equal the scenario's `expect`, which tolean's model computed.
// `now()` in the query is replaced by the scenario's `now`, the value the
// model takes as its `now` argument. An error prints as `ERROR <sqlstate>`,
// and the failed statement changes nothing.
package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"
)

type cluster struct {
	dir  string
	sock string
	port string
}

func start() (*cluster, error) {
	dir, err := os.MkdirTemp("", "tolean-pg-")
	if err != nil {
		return nil, err
	}
	c := &cluster{dir: dir, sock: filepath.Join(dir, "sock"), port: "25433"}
	if err := os.Mkdir(c.sock, 0o700); err != nil {
		return nil, err
	}
	data := filepath.Join(dir, "data")
	if out, err := exec.Command("initdb", "-D", data, "-U", "postgres", "--no-locale", "-E", "UTF8").CombinedOutput(); err != nil {
		return nil, fmt.Errorf("initdb: %v\n%s", err, out)
	}
	opts := fmt.Sprintf("-k %s -p %s -c listen_addresses=''", c.sock, c.port)
	if out, err := exec.Command("pg_ctl", "-D", data, "-o", opts, "-l", filepath.Join(dir, "log"), "-w", "start").CombinedOutput(); err != nil {
		return nil, fmt.Errorf("pg_ctl start: %v\n%s", err, out)
	}
	return c, nil
}

func (c *cluster) stop() {
	_ = exec.Command("pg_ctl", "-D", filepath.Join(c.dir, "data"), "-m", "immediate", "stop").Run()
	_ = os.RemoveAll(c.dir)
}

// psql runs SQL and returns its unaligned output, one row per line, with `|`
// between columns.
func (c *cluster) psql(stopOnError bool, args ...string) (string, string, error) {
	base := []string{"-h", c.sock, "-p", c.port, "-U", "postgres", "-d", "postgres", "-X", "-q", "-A", "-t",
		"-v", "VERBOSITY=sqlstate"}
	if stopOnError {
		base = append(base, "-v", "ON_ERROR_STOP=1")
	}
	cmd := exec.Command("psql", append(base, args...)...)
	var out, errb bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &errb
	err := cmd.Run()
	return out.String(), errb.String(), err
}

func (c *cluster) query(sql string) ([][]string, error) {
	out, stderr, err := c.psql(true, "-c", sql)
	if err != nil {
		return nil, fmt.Errorf("%v: %s", err, stderr)
	}
	var rows [][]string
	for _, line := range strings.Split(strings.TrimRight(out, "\n"), "\n") {
		if line != "" {
			rows = append(rows, strings.Split(line, "|"))
		}
	}
	return rows, nil
}

func (c *cluster) migrate(files []string, keepGoing bool) error {
	for _, f := range files {
		_, stderr, err := c.psql(!keepGoing, "-f", f)
		if err != nil {
			return fmt.Errorf("%s: %v\n%s", f, err, stderr)
		}
		if stderr != "" && keepGoing {
			fmt.Fprintf(os.Stderr, "%s: skipped failing statements:\n%s", f, stderr)
		}
	}
	return nil
}

func quoteLit(s string) string { return "'" + strings.ReplaceAll(s, "'", "''") + "'" }

func columnNames(c *cluster, table string, attnums string) ([]string, error) {
	rows, err := c.query(fmt.Sprintf(
		`SELECT a.attname FROM unnest('%s'::int2[]) WITH ORDINALITY k(n, i)
		 JOIN pg_attribute a ON a.attrelid = %s::regclass AND a.attnum = k.n ORDER BY k.i`,
		attnums, quoteLit(table)))
	if err != nil {
		return nil, err
	}
	var names []string
	for _, r := range rows {
		names = append(names, r[0])
	}
	return names, nil
}

func describeTable(c *cluster, table string) ([]string, []string, error) {
	var lines []string
	var refs []string
	lines = append(lines, "table "+table)
	cols, err := c.query(fmt.Sprintf(
		`SELECT attname, format_type(atttypid, atttypmod), attnotnull, atthasdef FROM pg_attribute
		 WHERE attrelid = %s::regclass AND attnum > 0 AND NOT attisdropped ORDER BY attnum`, quoteLit(table)))
	if err != nil {
		return nil, nil, err
	}
	for _, r := range cols {
		line := "  column " + r[0] + " " + r[1]
		if r[2] == "t" {
			line += " not null"
		}
		if r[3] == "t" {
			line += " default"
		}
		lines = append(lines, line)
	}
	cons, err := c.query(fmt.Sprintf(
		`SELECT contype, conkey, COALESCE(confrelid::regclass::text, ''), COALESCE(confkey::text, ''), confdeltype
		 FROM pg_constraint WHERE conrelid = %s::regclass ORDER BY contype, conkey::text`, quoteLit(table)))
	if err != nil {
		return nil, nil, err
	}
	var fks, uniques []string
	checks := 0
	for _, r := range cons {
		names, err := columnNames(c, table, r[1])
		if err != nil {
			return nil, nil, err
		}
		switch r[0] {
		case "p":
			lines = append(lines, "  primary key ("+strings.Join(names, ", ")+")")
		case "f":
			refNames, err := columnNames(c, r[2], r[3])
			if err != nil {
				return nil, nil, err
			}
			action := map[string]string{"c": " on delete cascade", "r": " on delete restrict", "n": " on delete set null"}[r[4]]
			fks = append(fks, "  foreign key ("+strings.Join(names, ", ")+") references "+r[2]+" ("+strings.Join(refNames, ", ")+")"+action)
			refs = append(refs, r[2])
		case "u":
			uniques = append(uniques, "  unique ("+strings.Join(names, ", ")+")")
		case "c":
			checks++
		}
	}
	idx, err := c.query(fmt.Sprintf(
		`SELECT i.indkey::text, i.indpred IS NOT NULL FROM pg_index i
		 WHERE i.indrelid = %s::regclass AND i.indisunique AND NOT i.indisprimary
		 AND NOT EXISTS (SELECT 1 FROM pg_constraint c WHERE c.conindid = i.indexrelid)`, quoteLit(table)))
	if err != nil {
		return nil, nil, err
	}
	for _, r := range idx {
		keys := "{" + strings.ReplaceAll(r[0], " ", ",") + "}"
		names, err := columnNames(c, table, keys)
		if err != nil {
			return nil, nil, err
		}
		line := "  unique (" + strings.Join(names, ", ") + ")"
		if r[1] == "t" {
			line += " partial"
		}
		uniques = append(uniques, line)
	}
	sort.Strings(fks)
	sort.Strings(uniques)
	lines = append(lines, fks...)
	lines = append(lines, uniques...)
	if checks > 0 {
		lines = append(lines, fmt.Sprintf("  checks %d", checks))
	}
	return lines, refs, nil
}

func describe(c *cluster, roots []string) (string, error) {
	seen := map[string]bool{}
	todo := append([]string{}, roots...)
	var tables []string
	for len(todo) > 0 {
		t := todo[0]
		todo = todo[1:]
		if seen[t] {
			continue
		}
		seen[t] = true
		tables = append(tables, t)
		_, refs, err := describeTable(c, t)
		if err != nil {
			return "", err
		}
		todo = append(todo, refs...)
	}
	sort.Strings(tables)
	var lines []string
	for _, t := range tables {
		ls, _, err := describeTable(c, t)
		if err != nil {
			return "", err
		}
		lines = append(lines, ls...)
	}
	quoted := make([]string, len(tables))
	for i, t := range tables {
		quoted[i] = quoteLit(t)
	}
	enums, err := c.query(fmt.Sprintf(
		`SELECT t.typname, string_agg(e.enumlabel, ',' ORDER BY e.enumsortorder) FROM pg_type t
		 JOIN pg_enum e ON e.enumtypid = t.oid
		 WHERE t.oid IN (SELECT atttypid FROM pg_attribute WHERE attrelid IN (%s) AND attnum > 0 AND NOT attisdropped)
		 GROUP BY t.typname ORDER BY t.typname`,
		strings.Join(func() []string {
			r := make([]string, len(quoted))
			for i, q := range quoted {
				r[i] = q + "::regclass"
			}
			return r
		}(), ", ")))
	if err != nil {
		return "", err
	}
	for _, r := range enums {
		lines = append(lines, "enum "+r[0]+" "+r[1])
	}
	return strings.Join(lines, "\n"), nil
}

type options struct {
	keepGoing  bool
	tables     []string
	migrations []string
	queries    []string
	scenarios  string
}

type scenario struct {
	Name   string            `json:"name"`
	Query  string            `json:"query"`
	Kind   string            `json:"kind"`
	Args   map[string]string `json:"args"`
	Now    string            `json:"now"`
	Setup  []string          `json:"setup"`
	State  string            `json:"state"`
	Expect string            `json:"expect"`
}

var argPattern = regexp.MustCompile(`sqlc\.n?arg\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)`)
var nowPattern = regexp.MustCompile(`(?i)\bnow\(\)`)
var errorPattern = regexp.MustCompile(`ERROR:\s+([0-9A-Z]{5})`)

// namedQueries reads sqlc query files: each `-- name: Name :kind` comment
// names the statement after it.
func namedQueries(files []string) (map[string]string, error) {
	out := map[string]string{}
	for _, f := range files {
		src, err := os.ReadFile(f)
		if err != nil {
			return nil, err
		}
		name := ""
		var body strings.Builder
		flush := func() {
			if name != "" {
				out[name] = strings.TrimRight(strings.TrimSpace(body.String()), ";")
			}
			body.Reset()
		}
		for _, line := range strings.Split(string(src), "\n") {
			trimmed := strings.TrimSpace(line)
			if strings.HasPrefix(trimmed, "-- name:") {
				flush()
				fields := strings.Fields(strings.TrimPrefix(trimmed, "-- name:"))
				name = fields[0]
				continue
			}
			body.WriteString(line + "\n")
		}
		flush()
	}
	return out, nil
}

func runScenarios(c *cluster, o options) error {
	queries, err := namedQueries(o.queries)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(o.scenarios)
	if err != nil {
		return err
	}
	var all []scenario
	var script strings.Builder
	script.WriteString("\\set ON_ERROR_ROLLBACK on\nSET TimeZone = 'UTC';\n")
	for i, line := range strings.Split(strings.TrimSpace(string(data)), "\n") {
		var sc scenario
		if err := json.Unmarshal([]byte(line), &sc); err != nil {
			return fmt.Errorf("scenario %d: %v", i+1, err)
		}
		text, ok := queries[sc.Query]
		if !ok {
			return fmt.Errorf("scenario %s: no query %s", sc.Name, sc.Query)
		}
		var missing []string
		text = argPattern.ReplaceAllStringFunc(text, func(m string) string {
			name := argPattern.FindStringSubmatch(m)[1]
			v, ok := sc.Args[name]
			if !ok {
				missing = append(missing, name)
			}
			return v
		})
		if len(missing) > 0 {
			return fmt.Errorf("scenario %s: no value for %v", sc.Name, missing)
		}
		text = nowPattern.ReplaceAllString(text, sc.Now)
		all = append(all, sc)
		fmt.Fprintf(&script, "BEGIN;\n")
		for _, st := range sc.Setup {
			script.WriteString(st + ";\n")
		}
		fmt.Fprintf(&script, "\\echo ===%d\n%s;\n", i, text)
		if sc.Kind == "execrows" {
			script.WriteString("\\echo :ROW_COUNT\n")
		}
		fmt.Fprintf(&script, "\\echo ---state\n%s;\nROLLBACK;\n", sc.State)
	}
	path := filepath.Join(c.dir, "scenarios.sql")
	if err := os.WriteFile(path, []byte(script.String()), 0o600); err != nil {
		return err
	}
	base := []string{"-h", c.sock, "-p", c.port, "-U", "postgres", "-d", "postgres", "-X", "-q", "-A", "-t",
		"-v", "VERBOSITY=sqlstate", "-f", path}
	cmd := exec.Command("psql", base...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	_ = cmd.Run()
	// Split the output at the markers.
	results := map[int][]string{}
	current := -1
	for _, line := range strings.Split(out.String(), "\n") {
		var n int
		if _, err := fmt.Sscanf(line, "===%d", &n); err == nil && strings.HasPrefix(line, "===") {
			current = n
			continue
		}
		if current < 0 || line == "" {
			continue
		}
		if m := errorPattern.FindStringSubmatch(line); m != nil {
			line = "ERROR " + m[1]
		}
		results[current] = append(results[current], line)
	}
	failed := 0
	for i, sc := range all {
		got := strings.Join(results[i], "\n")
		if got != strings.TrimRight(sc.Expect, "\n") {
			failed++
			if failed <= 5 {
				fmt.Printf("DIFF %s\n  postgres: %q\n  model:    %q\n", sc.Name, got, sc.Expect)
			}
		}
	}
	fmt.Printf("checked %d scenarios against PostgreSQL, %d differences\n", len(all), failed)
	if failed > 0 {
		return fmt.Errorf("the model and PostgreSQL disagree")
	}
	return nil
}

func parse(args []string) options {
	var o options
	var list *[]string
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "--keep-going":
			o.keepGoing = true
		case "--table":
			i++
			o.tables = append(o.tables, args[i])
			list = nil
		case "--migrations":
			list = &o.migrations
		case "--queries":
			list = &o.queries
		case "--scenarios":
			i++
			o.scenarios = args[i]
			list = nil
		default:
			if list == nil {
				fmt.Fprintf(os.Stderr, "unexpected argument %q\n", args[i])
				os.Exit(2)
			}
			*list = append(*list, args[i])
		}
	}
	return o
}

const tolean = "../../.lake/build/bin/tolean"

func checkCorpus(dir string) error {
	argText, err := os.ReadFile(filepath.Join(dir, "args"))
	if err != nil {
		return err
	}
	lines := strings.Split(strings.TrimSpace(string(argText)), "\n")
	if len(lines) < 2 {
		return fmt.Errorf("args needs two lines")
	}
	first := strings.Fields(lines[0])
	ns, queryOpts := first[0], first[1:]
	tableOpts := strings.Fields(lines[1])
	migrations, _ := filepath.Glob(filepath.Join(dir, "migrations", "*.up.sql"))
	sort.Strings(migrations)
	queryFiles, _ := filepath.Glob(filepath.Join(dir, "*.sql"))
	tmp, err := os.MkdirTemp("", "tolean-sql-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(tmp)
	// 1. The translation equals the committed file.
	out := filepath.Join(tmp, ns+".lean")
	args := append([]string{"translate-sql", out, ns}, queryOpts...)
	args = append(append(append(args, "--queries"), queryFiles...), "--migrations")
	args = append(args, migrations...)
	if msg, err := exec.Command(tolean, args...).CombinedOutput(); err != nil {
		return fmt.Errorf("tolean refused it: %s", msg)
	}
	got, _ := os.ReadFile(out)
	want, err := os.ReadFile(filepath.Join(dir, ns+".lean"))
	if err != nil || !bytes.Equal(got, want) {
		return fmt.Errorf("the translation differs from %s", filepath.Join(dir, ns+".lean"))
	}
	// 2. Lean compiles it.
	lean := exec.Command("lake", "env", "lean", out)
	lean.Dir = "../.."
	if msg, err := lean.CombinedOutput(); err != nil {
		return fmt.Errorf("Lean refused the translation:\n%s", msg)
	}
	// 3. The schema matches the catalog.
	c, err := start()
	if err != nil {
		return err
	}
	defer c.stop()
	if err := c.migrate(migrations, false); err != nil {
		return err
	}
	var tables []string
	for i := 0; i+1 < len(tableOpts); i += 2 {
		tables = append(tables, tableOpts[i+1])
	}
	pgSchema, err := describe(c, tables)
	if err != nil {
		return err
	}
	schemaArgs := append(append([]string{"sql-schema"}, tableOpts...), "--migrations")
	leanSchema, err := exec.Command(tolean, append(schemaArgs, migrations...)...).Output()
	if err != nil {
		return fmt.Errorf("tolean sql-schema: %v", err)
	}
	if strings.TrimSpace(string(leanSchema)) != strings.TrimSpace(pgSchema) {
		return fmt.Errorf("the schema differs from PostgreSQL's catalog:\n--- tolean\n%s\n--- postgres\n%s", leanSchema, pgSchema)
	}
	// 4. The scenarios agree with PostgreSQL.
	scenarioLean := filepath.Join(tmp, "Scenarios.lean")
	extra, err := os.ReadFile(filepath.Join(dir, "Scenarios.lean"))
	if err != nil {
		return err
	}
	if err := os.WriteFile(scenarioLean, append(got, extra...), 0o600); err != nil {
		return err
	}
	scenarios := filepath.Join(tmp, "scenarios.jsonl")
	gen := exec.Command("lake", "env", "lean", scenarioLean)
	gen.Dir = "../.."
	gen.Env = append(os.Environ(), "TOLEAN_SCENARIOS="+scenarios)
	if msg, err := gen.CombinedOutput(); err != nil {
		return fmt.Errorf("Scenarios.lean failed:\n%s", msg)
	}
	return runScenarios(c, options{queries: queryFiles, scenarios: scenarios})
}

// checkReject requires tolean to refuse the directory's queries with the
// message in `expect`.
func checkReject(dir string) error {
	argText, err := os.ReadFile(filepath.Join(dir, "args"))
	if err != nil {
		return err
	}
	expect, err := os.ReadFile(filepath.Join(dir, "expect"))
	if err != nil {
		return err
	}
	first := strings.Fields(strings.TrimSpace(string(argText)))
	migrations, _ := filepath.Glob(filepath.Join(dir, "migrations", "*.up.sql"))
	sort.Strings(migrations)
	queryFiles, _ := filepath.Glob(filepath.Join(dir, "*.sql"))
	args := append([]string{"translate-sql", os.DevNull, first[0]}, first[1:]...)
	args = append(append(append(args, "--queries"), queryFiles...), "--migrations")
	args = append(args, migrations...)
	out, err := exec.Command(tolean, args...).CombinedOutput()
	if err == nil {
		return fmt.Errorf("tolean accepted it")
	}
	if !strings.Contains(string(out), strings.TrimSpace(string(expect))) {
		return fmt.Errorf("want %q, got %q", strings.TrimSpace(string(expect)), strings.TrimSpace(string(out)))
	}
	return nil
}

// checkIsolation checks, on the real server, the READ COMMITTED behavior that
// tolean/Sql/Spec/ReadCommitted.lean models. Two transactions each take 20
// from a counter with 30 left:
//
//   - With a guarded UPDATE, the second waits for the first, re-checks its
//     WHERE on the new row, and changes nothing: 10 are left.
//   - When each reads first and then writes without a guard, both write, and
//     -10 are left: READ COMMITTED does not protect a write that depends on an
//     earlier read, which is why the translator refuses one.
func checkIsolation() error {
	c, err := start()
	if err != nil {
		return err
	}
	defer c.stop()
	if _, err := c.query("CREATE TABLE counters (id int PRIMARY KEY, used bigint NOT NULL, cap bigint NOT NULL); " +
		"INSERT INTO counters VALUES (1, 0, 30), (2, 0, 30)"); err != nil {
		return err
	}
	guarded := "BEGIN ISOLATION LEVEL READ COMMITTED; " +
		"UPDATE counters SET used = used + 20 WHERE id = 1 AND cap - used >= 20 RETURNING 'took'; "
	first := make(chan string, 1)
	go func() {
		out, _, _ := c.psql(true, "-c", guarded+"SELECT pg_sleep(1.5); COMMIT;")
		first <- out
	}()
	time.Sleep(400 * time.Millisecond)
	second, _, err := c.psql(true, "-c", guarded+"COMMIT;")
	if err != nil {
		return err
	}
	if out := <-first; !strings.Contains(out, "took") {
		return fmt.Errorf("the first guarded update did not take: %q", out)
	}
	if strings.Contains(second, "took") {
		return fmt.Errorf("the second guarded update took after the first committed")
	}
	left, err := c.query("SELECT cap - used FROM counters WHERE id = 1")
	if err != nil {
		return err
	}
	if left[0][0] != "10" {
		return fmt.Errorf("guarded updates left %s, want 10", left[0][0])
	}
	done := make(chan error, 2)
	for i := 0; i < 2; i++ {
		go func() {
			read, _, err := c.psql(true, "-c", "SELECT cap - used FROM counters WHERE id = 2")
			if err != nil {
				done <- err
				return
			}
			time.Sleep(500 * time.Millisecond)
			if strings.TrimSpace(read) == "30" {
				_, _, err = c.psql(true, "-c", "UPDATE counters SET used = used + 20 WHERE id = 2")
			}
			done <- err
		}()
	}
	for i := 0; i < 2; i++ {
		if err := <-done; err != nil {
			return err
		}
	}
	left, err = c.query("SELECT cap - used FROM counters WHERE id = 2")
	if err != nil {
		return err
	}
	if left[0][0] != "-10" {
		return fmt.Errorf("read-then-write left %s, want -10", left[0][0])
	}
	return nil
}

func main() {
	if len(os.Args) >= 2 && os.Args[1] == "corpus" {
		dirs, _ := filepath.Glob("corpus/*/args")
		failed := 0
		for _, a := range dirs {
			dir := filepath.Dir(a)
			if err := checkCorpus(dir); err != nil {
				fmt.Printf("FAIL %s: %v\n", dir, err)
				failed++
			}
		}
		rejects, _ := filepath.Glob("reject/*/expect")
		for _, e := range rejects {
			dir := filepath.Dir(e)
			if err := checkReject(dir); err != nil {
				fmt.Printf("FAIL %s: %v\n", dir, err)
				failed++
			}
		}
		if err := checkIsolation(); err != nil {
			fmt.Printf("FAIL READ COMMITTED behavior: %v\n", err)
			failed++
		}
		fmt.Printf("corpus: %d directories, %d refused, READ COMMITTED behavior checked, %d failures\n",
			len(dirs), len(rejects), failed)
		if failed > 0 {
			os.Exit(1)
		}
		return
	}
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: pgcheck schema|scenarios …")
		os.Exit(2)
	}
	o := parse(os.Args[2:])
	c, err := start()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	defer c.stop()
	if err := c.migrate(o.migrations, o.keepGoing); err != nil {
		fmt.Fprintln(os.Stderr, err)
		c.stop()
		os.Exit(1)
	}
	switch os.Args[1] {
	case "schema":
		out, err := describe(c, o.tables)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			c.stop()
			os.Exit(1)
		}
		fmt.Println(out)
	case "scenarios":
		if err := runScenarios(c, o); err != nil {
			fmt.Fprintln(os.Stderr, err)
			c.stop()
			os.Exit(1)
		}
	default:
		fmt.Fprintf(os.Stderr, "unknown command %q\n", os.Args[1])
		c.stop()
		os.Exit(2)
	}
}
