// Command check compares tolean's Go parser with go/parser.
//
//   - corpus/parse/accept/*.go: both parsers accept the file, and the two
//     syntax trees are equal, spans included.
//   - corpus/parse/reject/*.go: tolean refuses the file. The first line is
//     `// expect: LINE:COL TEXT`, and tolean's message must start at LINE:COL
//     and contain TEXT.
//   - corpus/translate/*/: tolean translates the package's .go files with the
//     options in `args` (the namespace first), the result equals the
//     committed .lean file in the directory, and Lean compiles it.
//   - Any extra paths on the command line are checked like accepted files.
//
// Run it from tests/go after `lake build`:
//
//	go run ./check [file.go ...]
package main

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

const tolean = "../../.lake/build/bin/tolean"

func main() {
	goast := filepath.Join(os.TempDir(), "tolean-goast")
	if out, err := exec.Command("go", "build", "-o", goast, "./goast").CombinedOutput(); err != nil {
		fmt.Fprintf(os.Stderr, "build goast: %v\n%s", err, out)
		os.Exit(2)
	}
	accept, _ := filepath.Glob("corpus/parse/accept/*.go")
	reject, _ := filepath.Glob("corpus/parse/reject/*.go")
	accept = append(accept, os.Args[1:]...)
	failed := 0
	for _, path := range accept {
		if err := checkAccept(goast, path); err != nil {
			fmt.Printf("FAIL %s: %v\n", path, err)
			failed++
		}
	}
	for _, path := range reject {
		if err := checkReject(path); err != nil {
			fmt.Printf("FAIL %s: %v\n", path, err)
			failed++
		}
	}
	translate, _ := filepath.Glob("corpus/translate/*/args")
	for _, args := range translate {
		if err := checkTranslate(filepath.Dir(args)); err != nil {
			fmt.Printf("FAIL %s: %v\n", filepath.Dir(args), err)
			failed++
		}
	}
	fmt.Printf("corpus: %d accepted files, %d refused files, %d translated packages, %d failures\n",
		len(accept), len(reject), len(translate), failed)
	if failed > 0 {
		os.Exit(1)
	}
}

func run(name string, args ...string) (string, string, error) {
	var stdout, stderr bytes.Buffer
	cmd := exec.Command(name, args...)
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	err := cmd.Run()
	return stdout.String(), stderr.String(), err
}

func checkAccept(goast, path string) error {
	want, stderr, err := run(goast, path)
	if err != nil {
		return fmt.Errorf("go/parser: %s", strings.TrimSpace(stderr))
	}
	got, stderr, err := run(tolean, "parse", path)
	if err != nil {
		return fmt.Errorf("tolean refused it: %s", strings.TrimSpace(stderr))
	}
	if got == want {
		return nil
	}
	wantLines := strings.Split(want, "\n")
	gotLines := strings.Split(got, "\n")
	for i := 0; i < len(wantLines) && i < len(gotLines); i++ {
		if wantLines[i] != gotLines[i] {
			return fmt.Errorf("line %d differs:\n  go/parser: %s\n  tolean:    %s",
				i+1, wantLines[i], gotLines[i])
		}
	}
	return fmt.Errorf("go/parser printed %d lines, tolean %d", len(wantLines), len(gotLines))
}

func checkReject(path string) error {
	src, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	first, _, _ := strings.Cut(string(src), "\n")
	spec, ok := strings.CutPrefix(first, "// expect: ")
	if !ok {
		return fmt.Errorf("the first line must be `// expect: LINE:COL TEXT`")
	}
	pos, text, _ := strings.Cut(spec, " ")
	_, stderr, err := run(tolean, "parse", path)
	if err == nil {
		return fmt.Errorf("tolean accepted it")
	}
	prefix := path + ":" + pos + ": "
	message := strings.TrimSpace(stderr)
	if !strings.HasPrefix(message, prefix) || !strings.Contains(message, text) {
		return fmt.Errorf("want %q and %q, got %q", prefix, text, message)
	}
	return nil
}

func checkTranslate(dir string) error {
	argText, err := os.ReadFile(filepath.Join(dir, "args"))
	if err != nil {
		return err
	}
	fields := strings.Fields(string(argText))
	if len(fields) == 0 {
		return fmt.Errorf("args must start with the namespace")
	}
	ns, opts := fields[0], fields[1:]
	sources, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	expectedPath := filepath.Join(dir, ns+".lean")
	expected, err := os.ReadFile(expectedPath)
	if err != nil {
		return fmt.Errorf("missing %s", expectedPath)
	}
	out := filepath.Join(os.TempDir(), "tolean-"+ns+".lean")
	cmdArgs := append(append([]string{"translate-go"}, opts...), out, ns)
	cmdArgs = append(cmdArgs, sources...)
	if _, stderr, err := run(tolean, cmdArgs...); err != nil {
		return fmt.Errorf("tolean refused it: %s", strings.TrimSpace(stderr))
	}
	got, err := os.ReadFile(out)
	if err != nil {
		return err
	}
	if !bytes.Equal(got, expected) {
		return fmt.Errorf("the translation differs from %s", expectedPath)
	}
	lean := exec.Command("lake", "env", "lean", out)
	lean.Dir = "../.."
	if output, err := lean.CombinedOutput(); err != nil {
		return fmt.Errorf("Lean refused the translation:\n%s", output)
	}
	return nil
}
