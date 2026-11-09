"""
guard.py -- a function whose domain is narrower than its signature asserts it.

WHY THIS EXISTS.  A constant list sliced to a length it does not have returns a shorter list
and no error.  The value that comes back is of the right type, so nothing downstream can
tell, and a row prints a figure that the stated formula does not give -- with no assertion,
no correction, and no remark.  The domain the code actually supports was narrower than the
signature promised, and nothing said so.

TWO HALVES.

  1. An API.  @domain(pred, msg) wraps a function so that every call is checked against
     pred(*args) and fails loudly with msg naming the input.  guard(cond, msg) is an assert
     that survives `python -O`.

  2. A linter.  Reports every slice of a NAME-bound constant list/tuple by a variable
     ([:k], [k:], XS[:n]) and every constant sequence indexed by a loop variable, as rows,
     so a human decides whether the domain is guarded.

Rows, not counts.
"""
import ast, sys, functools
from pathlib import Path

def guard(cond, msg):
    if not cond:
        raise AssertionError(msg)

def domain(pred, msg="input outside the function's domain"):
    def deco(fn):
        @functools.wraps(fn)
        def inner(*a, **k):
            if not pred(*a, **k):
                raise AssertionError(f"{fn.__name__}: {msg}: args={a!r}")
            return fn(*a, **k)
        return inner
    return deco

def lint(paths):
    rows = []
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(p.rglob("*.py"))
        for f in files:
            try:
                tree = ast.parse(f.read_text(errors="replace"))
            except SyntaxError:
                continue
            consts = {}
            for node in ast.walk(tree):
                if isinstance(node, ast.Assign) and len(node.targets) == 1 \
                        and isinstance(node.targets[0], ast.Name) \
                        and isinstance(node.value, (ast.List, ast.Tuple)) \
                        and all(isinstance(e, ast.Constant) for e in node.value.elts):
                    consts[node.targets[0].id] = len(node.value.elts)
            for node in ast.walk(tree):
                if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Name) \
                        and node.value.id in consts:
                    sl = node.slice
                    is_var_slice = isinstance(sl, ast.Slice) and any(
                        isinstance(b, ast.Name) for b in (sl.lower, sl.upper) if b is not None)
                    is_var_index = isinstance(sl, ast.Name)
                    if is_var_slice or is_var_index:
                        rows.append((str(f), node.lineno, node.value.id, consts[node.value.id],
                                     "slice" if is_var_slice else "index"))
    for f, i, name, n, kind in rows:
        print(f"  unguarded-{kind}  {f}:{i}  {name} has {n} constant entries, {kind}d by a variable")
    print(f"\n  guard: {len(rows)} constant sequences sliced or indexed by a variable")
    return rows

if __name__ == "__main__":
    sys.exit(1 if lint(sys.argv[1:]) else 0)
