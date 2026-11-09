"""
predeclare.py -- a script that prints a verdict carries a prediction above it.

WHY THIS EXISTS.  A number can be reinterpreted after the fact, and a fluent reinterpretation
is indistinguishable on the page from a prediction that came true.  The only mechanical
defence is to have the failure condition on disk before the number exists: a declaration,
above the computation, of what the run predicts and what result would count as its failure.

WHAT IT CHECKS.  A file whose source prints a verdict word (HOLDS, FAILS, CONFIRMED,
REFUTED, SURVIVES, RESOLVES POSITIVE / NEGATIVE) must contain, in its module docstring or
in a print that precedes the first computation (the first for / while / def), one of the
declaration markers: PREDICT, DECLARED IN ADVANCE, "before the run", "before computing",
"would count as a failure", "would refute", "would kill", "kill".  A file with verdicts and
no declaration is a row.

Rows, not counts.
"""
import ast, re, sys
from pathlib import Path

VERDICT = re.compile(r"\b(HOLDS|FAILS|CONFIRMED|REFUTED|SURVIVES|RESOLVES NEGATIVE|RESOLVES POSITIVE)\b")
DECL = re.compile(r"PREDICT|DECLARED IN ADVANCE|before the run|before computing|before any|"
                  r"would count as a failure|would refute|would kill|kill-check|KILL", re.I)

def check(paths):
    rows = []
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(p.rglob("*.py"))
        for f in files:
            src = f.read_text(errors="replace")
            if not VERDICT.search(src):
                continue
            try:
                tree = ast.parse(src)
            except SyntaxError:
                continue
            doc = ast.get_docstring(tree) or ""
            # text of prints before the first loop/def
            head = []
            for node in tree.body:
                if isinstance(node, (ast.For, ast.While, ast.FunctionDef)):
                    break
                head.append(ast.get_source_segment(src, node) or "")
            if not DECL.search(doc) and not DECL.search("\n".join(head)):
                first = next((i for i, l in enumerate(src.splitlines(), 1) if VERDICT.search(l)), 0)
                rows.append((str(f), first, "prints a verdict; no prediction or failure condition declared above the computation"))
    for f, i, d in rows:
        print(f"  undeclared-verdict  {f}:{i}  {d}")
    print(f"\n  predeclare: {len(rows)} files print a verdict with no declaration")
    return rows

if __name__ == "__main__":
    sys.exit(1 if check(sys.argv[1:]) else 0)
