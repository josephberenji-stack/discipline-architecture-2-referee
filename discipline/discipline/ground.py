"""
ground.py -- a claim-bearing file builds its own mathematics, from the ground up.

WHY THIS EXISTS.  A shared module makes one construction the silent premise of every file
that imports it.  When a shared module's documentation states one condition and its code
applies another, every file that imports it inherits the mismatch and none of them can see
it, because none of them contains the construction.  A file that builds its own objects can
be wrong on its own; it cannot be wrong on someone else's behalf.

THE RULE.  A file that declares a claim may cite, in a comment at the top, that it contains
mathematics mirroring a theorem, idea, variable or object found elsewhere -- but it builds
that mathematics out in the file, from the ground up, every time.  A citation is a mirror,
never a dependency.

WHAT IT CHECKS.  In every file that calls declare():

  1. Corpus import.  Any imported module that is neither the standard library nor
     `referee` is a row.  `referee` is the machinery, not the mathematics.
     Numerical libraries (numpy, scipy, sympy) are a row UNLESS the file carries a
     registered primitive (see primitive.py) that declares that library -- the primitive
     register is the separate, verified space, and carrying the verified text is what
     buys the import.
  2. Runtime read.  open()/read_text() on a project file is a row.
  3. Source extraction.  A read of another file's source, or an exec/eval of it.
  4. Missing MIRRORS block.  A file whose mathematics mirrors something named elsewhere
     must say so in a comment at the top: a line beginning `# MIRRORS` within the first
     40 lines, or a MIRRORS section in the module docstring.

WHAT A MIRROR IS.  A statement that this file's own construction reproduces an object
named elsewhere.  It carries no weight in the argument: delete every MIRRORS line and the
file computes exactly the same numbers, which is the point.

CONTROL.  `python3 -m discipline.ground --self` plants a self-contained file with a MIRRORS
block (must not row) and an importing file without one (must row twice).

Rows, not counts.
"""
import ast, re, sys
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

STDLIB = set(getattr(sys, "stdlib_module_names", ())) or {
    "sys", "os", "re", "io", "ast", "math", "cmath", "time", "random", "json",
    "itertools", "functools", "collections", "heapq", "bisect", "fractions",
    "decimal", "statistics", "pathlib", "typing", "textwrap", "tempfile",
    "subprocess", "contextlib", "operator", "copy", "string", "hashlib",
    "argparse", "csv", "datetime", "shutil", "glob", "pprint", "warnings",
    "unittest", "dataclasses", "enum", "abc", "traceback", "inspect", "pickle",
}
ALLOWED = STDLIB | {"referee", "discipline"}
NUMERIC = {"numpy", "scipy", "sympy"}
READ = re.compile(r"""(?:open\s*\(|read_text\s*\(|\bexec\s*\(|\bloads\s*\()""")
CORPUS_NAME = re.compile(r"[A-Za-z0-9_.\-]+\.(?:py|md|out|lean|v)")
MIRRORS = re.compile(r"^\s*#\s*MIRRORS\b|^MIRRORS\b", re.M)


def has_declare(tree):
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and (getattr(n.func, "attr", "") == "declare"
                                        or getattr(n.func, "id", "") == "declare"):
            return True
    return False


def _register_libs(start):
    """file -> libraries its carried primitives declare, from the primitive register."""
    import re as _re
    reg = config.registers(start) / "PRIMITIVES-REGISTER.md"
    if not reg.is_file():
        return {}
    byfile, cur, libs = {}, None, []
    for line in reg.read_text(errors="replace").splitlines():
        m = _re.match(r"^## (\S+)\s+`[0-9a-f]{8}`(?:\s+lib:(\S+))?", line)
        if m:
            cur, libs = m.group(1), (m.group(2).split(",") if m.group(2) else [])
            continue
        m = _re.match(r"^- (\S+):(\d+)\b", line)
        if m and cur:
            byfile.setdefault(m.group(1), set()).update(libs)
    return byfile


def check(paths):
    rows = []
    reg_libs = None
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(
            f for f in p.rglob("*.py") if not config.skipped(f))
        for f in files:
            src = f.read_text(errors="replace")
            try:
                tree = ast.parse(src)
            except SyntaxError:
                continue
            if not has_declare(tree):
                continue
            for n in ast.walk(tree):
                mods = []
                if isinstance(n, ast.Import):
                    mods = [(a.name.split(".")[0], n.lineno) for a in n.names]
                elif isinstance(n, ast.ImportFrom) and n.module:
                    mods = [(n.module.split(".")[0], n.lineno)]
                for m, ln in mods:
                    if m in ALLOWED:
                        continue
                    if m in NUMERIC:
                        if reg_libs is None:
                            reg_libs = _register_libs(f)
                        declared = reg_libs.get(f.name, set())
                        alias = {"numpy": {"numpy", "np"}, "scipy": {"scipy", "sp"},
                                 "sympy": {"sympy", "sp"}}[m]
                        if declared & alias:
                            continue
                        rows.append(("third-party-import", str(f), ln,
                                     f"'{m}' -- no registered primitive carried by "
                                     f"this file declares it"))
                        continue
                    rows.append(("corpus-import", str(f), ln,
                                 f"'{m}' -- the mathematics has to be in this file"))
            for i, line in enumerate(src.splitlines(), 1):
                if READ.search(line):
                    for nm in CORPUS_NAME.findall(line):
                        if nm != f.name:
                            rows.append(("runtime-read", str(f), i,
                                         f"reads {nm} while running"))
            doc = ast.get_docstring(tree) or ""
            head = "\n".join(src.splitlines()[:40])
            if not (MIRRORS.search(doc) or MIRRORS.search(head)):
                rows.append(("no-mirrors-block", str(f), 1,
                             "no '# MIRRORS' line in the first 40 lines and no "
                             "MIRRORS section in the docstring"))
    for kind, f, i, d in rows:
        print(f"  {kind:<20} {f}:{i}  {d}")
    print(f"\n  ground: {len(rows)} rows")
    return rows


def _self_test():
    import tempfile, collections
    d = Path(tempfile.mkdtemp())
    (d / "clean.py").write_text(
        '"""probe.\n\nMIRRORS.  The cycle it builds mirrors a result stated elsewhere; nothing is imported for it.\n"""\n'
        "import referee as R\nimport itertools\n"
        "R.declare('C1', predicts='x', kills='y')\n")
    (d / "dirty.py").write_text(
        '"""probe."""\nimport referee as R\nimport somewhere_else\n'
        "R.declare('C2', predicts='x', kills='y')\n")
    got = collections.Counter(r[0] for r in check([d]))
    assert got["corpus-import"] == 1, got
    assert got["no-mirrors-block"] == 1, got
    assert sum(got.values()) == 2, got
    print("\n  self-test: the self-contained file with a MIRRORS block does not row; "
          "the importing one rows twice.")
    return 0


if __name__ == "__main__":
    if "--self" in sys.argv:
        sys.exit(_self_test())
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
