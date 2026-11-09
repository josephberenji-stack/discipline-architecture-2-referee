"""statics.py -- the static half of the referee for the Python runs.

The runtime referee (`discipline/referee.py`) refuses verdicts with no declaration, literal verdicts and missing negative
controls while a run executes.  This module reads a run's source WITHOUT executing it and refuses what the runtime
referee cannot see.  Each check prints one line
    REFEREE<TAB>check<TAB>file:line<TAB>status<TAB>detail
with status PASS, FAIL or REVIEW (a person decides), and `main` exits 1 on any FAIL, 2 on REVIEW only, 0 otherwise.

THE CHECKS.
  P1 names       every name a run reads is bound somewhere it can see: an assignment, a def/class, a parameter, an
                 import, a comprehension or handler target, or a builtin.  An unbound name is a value the run never
                 defined.
  P2 imports     every import resolves to a named library (the standard library or an installed package) or to a
                 local file next to the run.  The import is located, never executed.
  P3 stubs       no function whose body is only `pass`, `...`, a docstring, `raise NotImplementedError`, or a
                 `return` of a constant; no TODO/FIXME/STUB/XXX marker.
  P4 self-check  no comparison of a value with itself (`x == x`, `f(a) <= f(a)`) and no comparison of two literals.
  P5 literal     no HOLDS/PASS/VERIFIED/CONFIRMED string printed outside a branch whose test is computed; no
     verdict     `verdict(...)` / `R.verdict(...)` whose `ok` argument is a constant or contains no name.
  P6 magic       a numeric literal other than 0, 1, 2, -1, 1/2 or 10 inside a verdict decision (the `ok` of verdict() or
     numbers     control(), or the test that chooses a verdict word), must be a named module-level UPPER_CASE constant (a `# source:` comment on its line is asked for, not checked).
  P7 expected    no `expected`/`EXPECTED`/`want`/`target` name bound to a literal and then compared to a result:  a
     outputs     hardcoded expected output can only agree with itself.  REVIEW, not FAIL, when the literal carries a
                 `# source:` comment (a published table may be the right comparison;  a person decides).
  P8 control     a run that prints a verdict must call `control(` (the runtime referee's negative control) at least
                 once:  a HOLDS that no failing case accompanies could not have been seen to fail.

`--mutate P<k>` switches check k off;  the self-test uses it to show that each planted fault is caught by the check
that is meant to catch it and by no accident of another.
"""
import ast, builtins, importlib.util, io, os, re, sys, tokenize

OFF = set()
NAMED_LIBS = {"numpy", "scipy", "sympy", "mpmath", "pandas", "matplotlib", "networkx", "numba", "gmpy2", "flint", "sage"}
TRIVIAL = {0, 1, 2, -1, 0.5, 10}
VERDICT_WORDS = re.compile(r"\b(HOLDS|VERIFIED|CONFIRMED)\b")
VERDICT_LINE = re.compile(r"^\s*\[?[A-Za-z0-9][\w\-.]*\]?\s+(HOLDS|VERIFIED|CONFIRMED)\b")
MARKERS = re.compile(r"#.*\b(TODO|FIXME|STUB|XXX)\b")
SOURCE_TAG = re.compile(r"#\s*source:", re.I)
EXPECT_NAMES = re.compile(r"^(expected|EXPECTED|want|WANT|target|TARGET|answer|ANSWER)(_\w*)?$")


def emit(out, check, where, status, detail):
    out.append((check, where, status, detail))


def bound_names(tree):
    """every name bound anywhere in the module (Python's scoping is not modelled finer than this;  a name bound
    only in another function is still reported if it is never bound at module level or in the reading scope)."""
    names = set(dir(builtins)) | {"__file__", "__name__", "__doc__", "__spec__"}
    for n in ast.walk(tree):
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(n.name)
            if not isinstance(n, ast.ClassDef):
                a = n.args
                for arg in a.posonlyargs + a.args + a.kwonlyargs + ([a.vararg] if a.vararg else []) + \
                        ([a.kwarg] if a.kwarg else []):
                    names.add(arg.arg)
        elif isinstance(n, ast.Lambda):
            for arg in n.args.args + n.args.kwonlyargs:
                names.add(arg.arg)
        elif isinstance(n, ast.Name) and isinstance(n.ctx, (ast.Store, ast.Del)):
            names.add(n.id)
        elif isinstance(n, (ast.Import, ast.ImportFrom)):
            for a in n.names:
                names.add((a.asname or a.name).split(".")[0])
        elif isinstance(n, ast.ExceptHandler) and n.name:
            names.add(n.name)
        elif isinstance(n, (ast.Global, ast.Nonlocal)):
            names.update(n.names)
        elif type(n).__name__ in ("MatchAs", "MatchStar", "MatchMapping") and getattr(n, "name", None):
            names.add(n.name)
    return names


def is_const(e):
    return isinstance(e, ast.Constant) or (isinstance(e, ast.UnaryOp) and isinstance(e.operand, ast.Constant))


def const_val(e):
    if isinstance(e, ast.Constant):
        return e.value
    if isinstance(e, ast.UnaryOp) and isinstance(e.op, ast.USub) and isinstance(e.operand, ast.Constant):
        v = e.operand.value
        return -v if isinstance(v, (int, float)) else None
    return None


def has_name(e):
    return any(isinstance(n, (ast.Name, ast.Attribute, ast.Call, ast.Subscript)) for n in ast.walk(e))


def check_file(path):
    out = []
    src = open(path, encoding="utf-8", errors="replace").read()
    lines = src.split("\n")
    try:
        tree = ast.parse(src, filename=path)
    except SyntaxError as e:
        emit(out, "P0", f"{path}:{e.lineno}", "FAIL", f"does not parse: {e.msg}")
        return out
    here = os.path.dirname(os.path.abspath(path))
    parents = {}
    for n in ast.walk(tree):
        for c in ast.iter_child_nodes(n):
            parents[c] = n

    # P1
    if "P1" not in OFF:
        bound = bound_names(tree)
        seen = set()
        for n in ast.walk(tree):
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load) and n.id not in bound and n.id not in seen:
                seen.add(n.id)
                emit(out, "P1", f"{path}:{n.lineno}", "FAIL", f"name `{n.id}` is read and never defined or imported")
        if not seen:
            emit(out, "P1", path, "PASS", "every name read is bound")

    # P2
    if "P2" not in OFF:
        bad = 0
        extra = [here]
        for n in ast.walk(tree):
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr in ("insert", "append") \
                    and ast.unparse(n.func.value) == "sys.path" and n.args:
                for c in ast.walk(n.args[-1]):
                    if isinstance(c, ast.Constant) and isinstance(c.value, str):
                        extra.append(os.path.join(here, c.value))
        for n in ast.walk(tree):
            mods = []
            if isinstance(n, ast.Import):
                mods = [a.name for a in n.names]
            elif isinstance(n, ast.ImportFrom) and n.level == 0 and n.module:
                mods = [n.module]
            for m in mods:
                top = m.split(".")[0]
                local = any(os.path.exists(os.path.join(d, top + ".py")) or os.path.isdir(os.path.join(d, top)) for d in extra)
                found = local
                if not found:
                    try:
                        found = importlib.util.find_spec(top) is not None
                    except (ImportError, ValueError):
                        found = False
                if not found and top in NAMED_LIBS:
                    emit(out, "P2", f"{path}:{n.lineno}", "REVIEW", f"import `{m}` is a named library not installed here")
                elif not found:
                    bad += 1
                    emit(out, "P2", f"{path}:{n.lineno}", "FAIL", f"import `{m}` resolves to no library and no local file")
        if not bad:
            emit(out, "P2", path, "PASS", "every import resolves")

    # P3
    if "P3" not in OFF:
        bad = 0
        for n in ast.walk(tree):
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)):
                body = [s for s in n.body if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                                                  and isinstance(s.value.value, str))]
                stub = False
                if not body:
                    stub = True
                elif len(body) == 1:
                    s = body[0]
                    if isinstance(s, ast.Pass) or (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                                                   and s.value.value is Ellipsis):
                        stub = True
                    elif isinstance(s, ast.Raise) and s.exc is not None and "NotImplementedError" in ast.unparse(s.exc):
                        stub = True
                    elif isinstance(s, ast.Return) and (s.value is None or is_const(s.value)):
                        stub = True
                if stub:
                    bad += 1
                    emit(out, "P3", f"{path}:{n.lineno}", "FAIL", f"function `{n.name}` is a stub")
        try:   # markers only in real comments (tokenize), not in strings or regexes that mention them
            comments = [(t.start[0], t.string) for t in tokenize.generate_tokens(io.StringIO(src).readline)
                        if t.type == tokenize.COMMENT]
        except (tokenize.TokenError, IndentationError, SyntaxError):
            comments = []
        for i, c in comments:
            if MARKERS.search(c):
                bad += 1
                emit(out, "P3", f"{path}:{i}", "FAIL", f"marker: {c.strip()[:80]}")
        if not bad:
            emit(out, "P3", path, "PASS", "no stub function, no TODO/FIXME/STUB marker")

    # P4
    if "P4" not in OFF:
        bad = 0
        for n in ast.walk(tree):
            if isinstance(n, ast.Compare):
                terms = [n.left] + n.comparators
                for a, b in zip(terms, terms[1:]):
                    if ast.dump(a) == ast.dump(b):
                        bad += 1
                        emit(out, "P4", f"{path}:{n.lineno}", "FAIL", f"compares a value with itself: {ast.unparse(n)[:80]}")
                    elif is_const(a) and is_const(b):
                        bad += 1
                        emit(out, "P4", f"{path}:{n.lineno}", "FAIL", f"compares two literals: {ast.unparse(n)[:80]}")
        if not bad:
            emit(out, "P4", path, "PASS", "no self-comparison")

    # P5
    prints_verdict = False
    if "P5" not in OFF:
        bad = 0
        for n in ast.walk(tree):
            if isinstance(n, ast.Call):
                fname = n.func.attr if isinstance(n.func, ast.Attribute) else getattr(n.func, "id", "")
                if fname == "verdict":
                    prints_verdict = True
                    ok = n.args[1] if len(n.args) > 1 else next((k.value for k in n.keywords if k.arg == "ok"), None)
                    if ok is not None and (is_const(ok) or not has_name(ok)):
                        bad += 1
                        emit(out, "P5", f"{path}:{n.lineno}", "FAIL", f"verdict with a constant ok: {ast.unparse(ok)[:60]}")
                if fname == "print":
                    for a in n.args:
                        lit = a.value if isinstance(a, ast.Constant) and isinstance(a.value, str) else None
                        if isinstance(a, ast.JoinedStr):
                            lit = "".join(v.value for v in a.values if isinstance(v, ast.Constant))
                        if lit and VERDICT_LINE.search(lit):
                            prints_verdict = True
                            p, guarded = parents.get(n), False
                            while p is not None:
                                if isinstance(p, (ast.If, ast.IfExp, ast.While)) and has_name(p.test):
                                    guarded = True
                                    break
                                p = parents.get(p)
                            if not guarded:
                                bad += 1
                                emit(out, "P5", f"{path}:{n.lineno}", "FAIL",
                                     f"prints `{VERDICT_LINE.search(lit).group(1)}` with no computed test above it")
            if isinstance(n, ast.IfExp) and isinstance(n.body, ast.Constant) and isinstance(n.body.value, str) \
                    and VERDICT_WORDS.search(n.body.value):
                prints_verdict = True
                if not has_name(n.test):
                    bad += 1
                    emit(out, "P5", f"{path}:{n.lineno}", "FAIL", "verdict word chosen by a constant test")
        if not bad:
            emit(out, "P5", path, "PASS", "every verdict comes from a computed test")

    # P6
    if "P6" not in OFF:
        bad = 0
        named = {}
        for s in tree.body:
            if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) \
                    and s.targets[0].id.isupper():
                named[s.targets[0].id] = SOURCE_TAG.search(lines[s.lineno - 1]) is not None
        for name, sourced in named.items():
            if not sourced:
                pass
        decisions = []
        for n in ast.walk(tree):
            if isinstance(n, ast.Call):
                fname = n.func.attr if isinstance(n.func, ast.Attribute) else getattr(n.func, "id", "")
                if fname in ("verdict", "control"):
                    ok = n.args[1] if len(n.args) > 1 else next((k.value for k in n.keywords if k.arg == "ok"), None)
                    if ok is not None:
                        decisions.append(ok)
            if isinstance(n, ast.IfExp) and isinstance(n.body, ast.Constant) and isinstance(n.body.value, str) \
                    and VERDICT_WORDS.search(n.body.value):
                decisions.append(n.test)
        for d in decisions:
          for n in ast.walk(d):
            if isinstance(n, ast.Compare):
                for t in [n.left] + n.comparators:
                    v = const_val(t)
                    if isinstance(v, (int, float)) and not isinstance(v, bool) and v not in TRIVIAL:
                        bad += 1
                        emit(out, "P6", f"{path}:{n.lineno}", "FAIL",
                             f"magic number {v} in a comparison; name it as an UPPER_CASE constant with `# source:`")

        if not bad:
            emit(out, "P6", path, "PASS", "no unexplained number in a verdict decision")

    # P7
    if "P7" not in OFF:
        bad = rev = 0
        lits = {}
        for n in ast.walk(tree):
            if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                    and EXPECT_NAMES.match(n.targets[0].id) and (is_const(n.value) or (
                        isinstance(n.value, (ast.List, ast.Tuple, ast.Dict, ast.Set)) and
                        all(is_const(x) for x in ast.walk(n.value) if isinstance(x, ast.expr) and x is not n.value
                            and not isinstance(x, (ast.List, ast.Tuple, ast.Dict, ast.Set, ast.Load))))):
                lits[n.targets[0].id] = (n.lineno, SOURCE_TAG.search(lines[n.lineno - 1]) is not None)
        writes = {}
        for n in ast.walk(tree):
            if isinstance(n, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                tg = n.targets if isinstance(n, ast.Assign) else [n.target]
                for t in tg:
                    if isinstance(t, ast.Name):
                        writes[t.id] = writes.get(t.id, 0) + 1
            if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and isinstance(n.func.value, ast.Name) \
                    and n.func.attr in ("append", "extend", "add", "update", "insert"):
                writes[n.func.value.id] = writes.get(n.func.value.id, 0) + 1
        lits = {k: v for k, v in lits.items() if writes.get(k, 0) <= 1}
        for n in ast.walk(tree):
            if isinstance(n, ast.Compare):
                for t in [n.left] + n.comparators:
                    if isinstance(t, ast.Name) and t.id in lits:
                        ln, sourced = lits[t.id]
                        if sourced or t.id.isupper():
                            rev += 1
                            emit(out, "P7", f"{path}:{n.lineno}", "REVIEW",
                                 f"compares to the declared constant `{t.id}` (line {ln}): a person checks it was declared before the run and where it comes from")
                        else:
                            bad += 1
                            emit(out, "P7", f"{path}:{n.lineno}", "FAIL",
                                 f"compares to the hardcoded expected output `{t.id}` (line {ln})")
        if not bad and not rev:
            emit(out, "P7", path, "PASS", "no hardcoded expected output compared")

    # P8
    if "P8" not in OFF:
        calls = {(n.func.attr if isinstance(n.func, ast.Attribute) else getattr(n.func, "id", ""))
                 for n in ast.walk(tree) if isinstance(n, ast.Call)}
        if prints_verdict or "verdict" in calls:
            if "control" in calls:
                emit(out, "P8", path, "PASS", "a negative control is called")
            else:
                emit(out, "P8", path, "FAIL", "prints a verdict and calls no control(): the HOLDS could not be seen to fail")
        else:
            emit(out, "P8", path, "PASS", "prints no verdict")
    return out


def selftest():
    """each planted control must fail the check named in its file name; the clean run must pass every check;  then
    each check is switched off in turn and its control must get through."""
    d = os.path.join(os.path.dirname(os.path.abspath(__file__)), "controls", "py")
    ctrls = sorted(f for f in os.listdir(d) if f.startswith("ctrl_p"))
    def run():
        bad = 0
        for f in ctrls:
            k = "P" + f.split("_")[1][1:]
            st = {c: s_ for c, _, s_, _ in check_file(os.path.join(d, f)) if c == k}
            ok = "FAIL" in st.values() or any(s_ == "FAIL" for c, _, s_, _ in check_file(os.path.join(d, f)) if c == k)
            bad += not ok
            print(f"SELFTEST\t{f}\t{k}\t{'caught' if ok else 'NOT CAUGHT'}")
        rows = check_file(os.path.join(d, "good_run.py"))
        clean = all(s_ == "PASS" for _, _, s_, _ in rows)
        bad += not clean
        print(f"SELFTEST\tgood_run.py\tall\t{'clean' if clean else 'FLAGGED: ' + str([r for r in rows if r[2] != 'PASS'])}")
        return bad
    if run():
        return 1
    survived = []
    for k in ["P1", "P2", "P3", "P4", "P5", "P6", "P7", "P8"]:
        OFF.clear(); OFF.add(k)
        f = next(x for x in ctrls if x.startswith("ctrl_p" + k[1:] + "_"))
        if not any(s_ == "FAIL" and c == k for c, _, s_, _ in check_file(os.path.join(d, f))):
            print(f"MUTATION\t{k} off: its control gets through, as it must")
        else:
            survived.append(k)
    OFF.clear()
    print("MUTATION\t" + ("every check is needed" if not survived else f"FAIL: {survived} still caught with the check off"))
    return 1 if survived else 0


def main(argv):
    if argv == ["--selftest"]:
        return selftest()
    files = []
    for a in argv:
        if a.startswith("--mutate="):
            OFF.update(a.split("=", 1)[1].split(","))
        elif os.path.isdir(a):
            for r, _, fs in os.walk(a):
                files += [os.path.join(r, f) for f in fs if f.endswith(".py")]
        else:
            files.append(a)
    worst = 0
    for f in sorted(files):
        for check, where, status, detail in check_file(f):
            print(f"REFEREE\t{check}\t{where}\t{status}\t{detail}")
            worst = max(worst, {"PASS": 0, "REVIEW": 2, "FAIL": 3}[status])
    return {0: 0, 2: 2, 3: 1}[worst]


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
