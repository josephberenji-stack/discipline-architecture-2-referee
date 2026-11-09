"""
noliteral.py -- no printed table column or verdict may be a constant.

WHY THIS EXISTS.  The rule "where prose and table disagree, the table is right" presumes the
table was computed.  A column that reads as a check can be a literal: a quantity printed as
a constant in the table that sits under the sentence claiming it never moves; 'YES' printed
in a column headed "contradiction?"; a literal True in a column that reads as a test.  Each
is believed because it is in a table, and nothing on the page distinguishes it from a
column the run produced.

WHAT IT CHECKS.  Every f-string that is an argument of print() is walked; each formatted
field whose expression is a constant (number, string, True/False/None, or a container of
constants) is reported as a row with file, line, the literal, and the format spec.  A
verdict string passed to print() that contains a verdict word (HOLDS, FAILS, PASS,
CONFIRMED, REFUTED, ...) with no formatted field at all is reported separately: a
conclusion that does not depend on any variable.

WHAT IT DOES NOT CHECK.  Headers.  A field whose format spec is a plain string alignment
(e.g. {'atoms':>9}) is a column header and is skipped.  A constant that is explicitly
labelled (const) in the surrounding text is skipped.

Rows, not counts.
"""
import ast, sys, re
from pathlib import Path

VERDICT = re.compile(r"\b(HOLDS|FAILS|PASS(?:ED)?|FAIL(?:ED)?|CONFIRMED|REFUTED|"
                     r"SURVIVES|TRUE|FALSE|YES|NO)\b")
# a whole printed sentence counts as a verdict only on the strong words
VERDICT_SENTENCE = re.compile(r"\b(HOLDS|FAILS|PASSES|CONFIRMED|REFUTED|SURVIVES|RESOLVES NEGATIVE|RESOLVES POSITIVE)\b")
HEADER_SPEC = re.compile(r"^[<>^]?\d+s?$")

def _is_const(node):
    if isinstance(node, ast.Constant):
        return True
    if isinstance(node, (ast.Tuple, ast.List)):
        return all(_is_const(e) for e in node.elts)
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
        return _is_const(node.operand)
    return False

def _const_repr(node):
    try:
        return repr(ast.literal_eval(node))
    except Exception:
        return ast.dump(node)[:40]

def _spec_text(fv):
    if fv.format_spec is None:
        return ""
    return "".join(v.value for v in fv.format_spec.values if isinstance(v, ast.Constant))

def check_file(path):
    rows = []
    try:
        tree = ast.parse(Path(path).read_text(), filename=str(path))
    except SyntaxError as e:
        return [{"file": str(path), "line": e.lineno, "kind": "syntax", "detail": str(e)}]
    src = Path(path).read_text().splitlines()
    for node in ast.walk(tree):
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "print"):
            continue
        for arg in node.args:
            if isinstance(arg, ast.JoinedStr):
                fields = [v for v in arg.values if isinstance(v, ast.FormattedValue)]
                for fv in fields:
                    if not _is_const(fv.value):
                        continue
                    spec = _spec_text(fv)
                    val = _const_repr(fv.value)
                    is_str = isinstance(fv.value, ast.Constant) and isinstance(fv.value.value, str)
                    # a constant string with a bare alignment spec and no verdict word is a header
                    if is_str and (spec == "" or HEADER_SPEC.match(spec)) \
                            and not VERDICT.search(fv.value.value):
                        continue
                    line = src[fv.lineno - 1] if fv.lineno - 1 < len(src) else ""
                    if "(const)" in line:
                        continue
                    rows.append({"file": str(path), "line": fv.lineno, "kind": "literal-field",
                                 "detail": f"{val} with spec '{spec}'"})
            elif isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                if VERDICT_SENTENCE.search(arg.value) and len(arg.value.strip()) < 200:
                    rows.append({"file": str(path), "line": arg.lineno, "kind": "constant-verdict",
                                 "detail": arg.value.strip().splitlines()[0][:90]})
    return rows

def main(paths):
    rows = []
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(p.rglob("*.py"))
        for f in files:
            rows += check_file(f)
    for r in rows:
        print(f"  {r['kind']:<17} {r['file']}:{r['line']}  {r['detail']}")
    print(f"\n  noliteral: {len(rows)} rows ({sum(r['kind']=='literal-field' for r in rows)} literal fields, "
          f"{sum(r['kind']=='constant-verdict' for r in rows)} constant verdicts)")
    return rows

if __name__ == "__main__":
    sys.exit(1 if main(sys.argv[1:]) else 0)
