"""forced.py -- was the outcome ever at risk?  The static half.

WHY THIS EXISTS.  referee.py refuses a verdict whose argument is a literal, and a mutation
pass can change the construction to see whether a claim can move.  Between the two there
is a gap: an argument that is computed by the letter but whose value was written into the
file -- an expected-answer table compared against itself, a threshold that is the answer,
a name that traces back through two assignments to a constant.  This walks the syntax and
prints those as rows.

KILL-CHECK, declared before any run.  What refutes a file's empirical standing is a row
here: a verdict argument that traces back only to constants, or a constant container
standing on one side of a comparison whose other side is computed.  A grid of INPUTS is
not a row -- a constant that is only ever iterated over is a parameter, and parameters are
allowed to be written down.  The distinction the checker makes is iterated (input) against
compared (expected output).

A second distinction the checker makes is declared against undeclared.  A prediction has
to be written down somewhere -- "the row is (1, 2, 1)" is the prediction, and comparing a
computed row against it is what a prediction is for.  So a constant that also appears in
the file's declare() text is the declared prediction and is not a row.  A constant that
appears only in the comparison is an expectation the file never committed to in advance,
and is.  Membership tests (in / not in) are filters, not comparisons against an answer,
and are not rows either.  Neither is an all-zero container OUTSIDE a claim-deciding test:
a comparison against the zero vector is an identity check, not an expected value.  Inside
a claim-deciding test it stays a row, because "the map is zero" is a claim like any other
and has to be declared.

WHAT IT CHECKS.
  A  verdict/control called with a constant second argument       (static)
  B  a constant container of 2 or more entries in a comparison whose
     value is NOT named in the file's own declare() text            (answer table)
  C  a verdict argument whose free names all trace back, through
     assignments, to constants and nothing else                   (traced)
  D  a comparison against an undeclared numeric literal in a test that
     decides a claim -- either inside the reported argument itself, or
     in an if whose body records a violating row for that claim.  A
     literal is a row unless it is 0, 1 or 2 -- structural (empty,
     singleton, pair) -- whether it is spelt 2 or 2.0.  Every other
     value, integer or float, is a chosen one.  A declared FRACTION
     declares the float it equals: "ratio = 1/2" declares 0.5, by exact
     arithmetic and no tolerance.
     A number used to truncate a printed line is not a row.        (threshold)
  E  a control() call with no `vacuous=` argument.  A control that agrees
     with the claim on some of its rows is silent on them, not failing, and
     the referee sees only pass or fail.  The count cannot be derived from the
     syntax, so the file has to state it; not stating it is the row.

CONTROL.  `python3 -m discipline.forced --self` plants a declared and an undeclared float
threshold in a scratch file; the declared one must not row and the undeclared one must.

Rows, not counts.
"""
import ast, re, sys
from pathlib import Path

REPORTERS = {"verdict", "control"}
# builtins are not bindings; a name that is only a builtin call must not rescue an
# argument that otherwise traces to literals.
BUILTINS = {"len", "sum", "all", "any", "abs", "sorted", "min", "max", "set", "list",
            "tuple", "dict", "int", "str", "bool", "range", "zip", "enumerate",
            "print", "map", "filter", "round", "divmod", "pow", "next", "iter"}


def _const_container(n):
    return isinstance(n, (ast.List, ast.Tuple, ast.Set)) and \
        len(n.elts) >= 2 and all(isinstance(e, ast.Constant) for e in n.elts)


def _is_literalish(n):
    return isinstance(n, ast.Constant) or _const_container(n) or (
        isinstance(n, (ast.List, ast.Tuple, ast.Set, ast.Dict)) and
        all(isinstance(e, ast.Constant) for e in getattr(n, "elts", []) or []))


def check(paths):
    rows = []
    files = []
    for p in paths:
        p = Path(p)
        files += [p] if p.is_file() else sorted(p.rglob("*.py"))
    for f in files:
        try:
            tree = ast.parse(f.read_text(errors="replace"))
        except SyntaxError:
            continue
        binds, iterated, mutated = {}, set(), set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign) and len(node.targets) == 1 and \
                    isinstance(node.targets[0], ast.Name):
                binds.setdefault(node.targets[0].id, []).append(node.value)
            # a name that is appended to, extended, or augmented is computed at
            # run time whatever its initial binding was -- an empty list literal
            # is a container, not an answer.
            if isinstance(node, ast.AugAssign) and isinstance(node.target, ast.Name):
                mutated.add(node.target.id)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and \
                    node.func.attr in ("append", "add", "extend", "update", "insert") and \
                    isinstance(node.func.value, ast.Name):
                mutated.add(node.func.value.id)
            if isinstance(node, (ast.For, ast.comprehension)):
                it = node.iter
                for nm in ast.walk(it):
                    if isinstance(nm, ast.Name):
                        iterated.add(nm.id)
        # A and C
        for node in ast.walk(tree):
            if not (isinstance(node, ast.Call) and
                    getattr(node.func, "id", getattr(node.func, "attr", "")) in REPORTERS):
                continue
            if len(node.args) < 2:
                continue
            arg = node.args[1]
            label = ast.unparse(node.args[0]) if node.args else "?"
            if isinstance(arg, ast.Constant):
                rows.append((f, node.lineno, "A", f"{label}: the reported argument is a literal"))
                continue
            names = {n.id for n in ast.walk(arg)
                     if isinstance(n, ast.Name) and n.id not in BUILTINS}
            seen, frontier, sources = set(), list(names), []
            while frontier:
                nm = frontier.pop()
                if nm in seen:
                    continue
                seen.add(nm)
                if nm in mutated:
                    sources.append((nm, "computed"))
                for v in binds.get(nm, []):
                    if nm not in mutated and _is_literalish(v):
                        sources.append((nm, "literal"))
                    else:
                        sources.append((nm, "computed"))
                        frontier += [x.id for x in ast.walk(v)
                                     if isinstance(x, ast.Name) and x.id not in BUILTINS]
                if nm not in binds:
                    sources.append((nm, "free"))
            kinds = {k for _, k in sources}
            if kinds and kinds <= {"literal"}:
                rows.append((f, node.lineno, "C",
                             f"{label}: every name in the reported argument traces to a literal"))
        # the file's own declared predictions, as text
        decl = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and \
                    getattr(node.func, "id", getattr(node.func, "attr", "")) == "declare":
                for x in list(node.args) + [k.value for k in node.keywords]:
                    if isinstance(x, ast.Constant) and isinstance(x.value, str):
                        decl.append(x.value)
                    else:
                        decl.append(ast.unparse(x))
        decl_text = " || ".join(decl)

        def declared_num(v):
            # a bare number, matched as its own token: "Q7" does not declare 7.
            forms = {str(v)}
            if isinstance(v, float) and v == int(v):
                forms.add(str(int(v)))
            for form in forms:
                if re.search(r"(?<![\w.])" + re.escape(form) + r"(?!\w)(?!\.\d)",
                             decl_text):
                    return True
            # a declared FRACTION is the same number as the float in the code:
            # "ratio = 1/2" declares 0.5.  Exact arithmetic, no tolerance.
            for num, den in re.findall(r"(?<![\w.])(\d+)\s*/\s*(\d+)(?!\.?\d)",
                                       decl_text):
                if int(den) and int(num) == v * int(den):
                    return True
            return False

        def declared(node_):
            body = ast.unparse(node_)
            inner = body.strip("[](){} ")
            squeezed = inner.replace(" ", "")
            return inner in decl_text or squeezed in decl_text.replace(" ", "")

        # which Compare nodes actually decide a claim
        claim_names = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and \
                    getattr(node.func, "id", getattr(node.func, "attr", "")) in \
                    (REPORTERS | {"rows"}):
                for x in node.args[1:]:
                    claim_names |= {y.id for y in ast.walk(x) if isinstance(y, ast.Name)}
        deciding = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.If):
                touched = set()
                for b in node.body:
                    for x in ast.walk(b):
                        if isinstance(x, ast.Call) and isinstance(x.func, ast.Attribute) \
                                and isinstance(x.func.value, ast.Name):
                            touched.add(x.func.value.id)
                        if isinstance(x, ast.AugAssign) and isinstance(x.target, ast.Name):
                            touched.add(x.target.id)
                if touched & claim_names:
                    deciding |= {id(x) for x in ast.walk(node.test)}
            if isinstance(node, ast.Call) and \
                    getattr(node.func, "id", getattr(node.func, "attr", "")) in REPORTERS \
                    and len(node.args) >= 2:
                deciding |= {id(x) for x in ast.walk(node.args[1])}

        # B and D
        for node in ast.walk(tree):
            if not isinstance(node, ast.Compare):
                continue
            if any(isinstance(op, (ast.In, ast.NotIn)) for op in node.ops):
                continue
            sides = [node.left] + list(node.comparators)
            for s in sides:
                all_zero = _const_container(s) and all(
                    e.value == 0 for e in s.elts)
                if _const_container(s) and not declared(s) and \
                        not (all_zero and id(node) not in deciding):
                    rows.append((f, getattr(node, "lineno", 0), "B",
                                 f"a {len(s.elts)}-entry constant container is compared: "
                                 f"{ast.unparse(s)[:60]}"))
                if isinstance(s, ast.Name) and s.id in binds and s.id not in iterated and \
                        s.id not in mutated and \
                        any(_const_container(v) and not declared(v) for v in binds[s.id]):
                    rows.append((f, getattr(node, "lineno", 0), "B",
                                 f"'{s.id}' is bound to a constant container and compared"))
                # 0, 1 and 2 are structural (empty, singleton, pair) whether
                # they are spelt 2 or 2.0; everything else is a chosen value.
                num = (isinstance(s, ast.Constant)
                       and isinstance(s.value, (int, float))
                       and not isinstance(s.value, bool)
                       and not (s.value == int(s.value) and abs(s.value) < 3))
                if num:
                    call = any(isinstance(x, ast.Call) for x in sides if x is not s)
                    if call and not declared_num(s.value) and id(node) in deciding:
                        rows.append((f, getattr(node, "lineno", 0), "D",
                                     f"a computed value is compared against the literal {s.value}"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Call) and \
                    getattr(node.func, "attr", getattr(node.func, "id", "")) == "control":
                if not any(kw.arg == "vacuous" for kw in node.keywords):
                    rows.append((f, node.lineno, "E",
                                 "a control with no vacuous= count: the referee "
                                 "cannot tell a silent row from a failing one"))
    for f, i, k, d in rows:
        print(f"  forced-{k}  {f}:{i}  {d}")
    print(f"\n  forced: {len(rows)} rows")
    return rows


def _self_test():
    """The D control, planted.  A float threshold declared as a fraction must NOT row;
    an undeclared one must.  Both are asserted."""
    import tempfile, collections
    d = Path(tempfile.mkdtemp())
    (d / "probe.py").write_text(
        '''"""probe."""
import referee as R
R.declare("C1", predicts="the ratio is 1/2 at every model",
          kills="any model whose ratio is not 1/2")
R.declare("C2", predicts="the other ratio is stable",
          kills="any model where it moves")
def measure():
    return 0.5
R.verdict("C1", measure() == 0.5, "declared as 1/2")
R.verdict("C2", measure() == 0.37, "never declared")
''')
    got = check([d / "probe.py"])
    lits = collections.Counter(r[3].rsplit(" ", 1)[-1] for r in got)
    assert lits["0.37"] == 1, got
    assert lits["0.5"] == 0, got
    print("\n  self-test: 0.5 declared as 1/2 does not row; 0.37 does.")
    return 0


if __name__ == "__main__":
    if "--self" in sys.argv:
        sys.exit(_self_test())
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
