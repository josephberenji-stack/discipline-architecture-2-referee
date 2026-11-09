"""reprleak.py -- a typed value is read only through a named translation, never through its storage.

WHY.  A project that wraps values in their own types (a residue mod n, a word of fixed width, an amount with a
currency, a quantity with a unit) does so because the bare integer underneath is not the value.  The failure this
check finds is the moment code steps around the type and reads the storage instead:  it prints the value in binary,
parses it back with int(s, 2), masks it with & or shifts it with <<, or unwraps it to a plain int and does arithmetic
on the result.  Each of those quietly drops the type's rules (its modulus, its width, its unit), and the code still
runs.  A language model writing code is especially prone to it, because the storage form is always one call away and
always type-checks.

WHAT IT CHECKS, in a file that opts in (below), outside the kernel's own definitions:
  base-conversion  bin(), oct(), hex(), int(s, 2|8|16), or a format of type b, o, x, X (f-string, str.format,
                   format(), %-format).  hex and x/X can be switched off for projects that print hex for people.
  raw-bitop        ^ & | ~ << >>.  Inside the kernel they may be the type's own operations;  outside they read the
                   storage.
  unwrap           an unwrap method (named in the policy, e.g. as_int) whose result feeds arithmetic, a comparison, or
                   a constructor of the type.  A value reaches another type only through a named translation.
  no-gate          the policy names a gate function (a one-time check of the kernel's invariants) and a file that
                   carries or imports the kernel never calls it.  A file opted in by the pragma alone is not asked.

OPT-IN.  The check is silent on a file unless the file opts in, so ordinary code that formats numbers is never read.
A file opts in when it carries the pragma `# reprleak: on`, or when it matches the policy's `opt_in`:  it defines a
top-level class of that name (`{"class": "LevelError"}`) or imports a module of that name (`{"import": "mylevels"}`).
A file that only defines a function with a kernel-like name does not opt in.

POLICY.  Read from `reprleak.json` in the registers directory (config.registers()), or from the file named by the
environment variable DISCIPLINE_REPRLEAK.  Every list ships empty;  with no policy the check reads only files that
carry the pragma, and the unwrap and gate rules are off.  Keys:
    opt_in        {"class": NAME} or {"import": NAME}, or null
    kernel        names whose bodies are the kernel and are not checked
    constructors  the type's constructors (for the unwrap rule)
    unwrap        unwrap method names, e.g. ["as_int"]
    gate          the gate function's name, or null
    translations  the named translations, quoted in the messages
    rules         {"base": true, "hex": true, "bitop": true, "unwrap": true, "gate": true}

DISPLAY.  A line that only shows a value to a person may carry `# reprleak: display`;  that line is not checked.

    python3 -m discipline.reprleak FILE ...    the rows
    python3 -m discipline.reprleak --self      the control:  one probe per rule rows once;  the clean probe rows nothing

Rows, not counts.
"""
import ast, json, os, re, sys
from pathlib import Path

try:
    from . import config
except ImportError:          # run as a script
    import config            # type: ignore

DEFAULT_RULES = {"base": True, "hex": True, "bitop": True, "unwrap": True, "gate": True}
EMPTY = {"opt_in": None, "kernel": [], "constructors": [], "unwrap": [], "gate": None, "translations": [],
         "rules": DEFAULT_RULES}
PRAGMA_ON = re.compile(r"#\s*reprleak:\s*on\b")
PRAGMA_DISPLAY = re.compile(r"#\s*reprleak:\s*display\b")
BITOPS = (ast.BitXor, ast.BitAnd, ast.BitOr, ast.LShift, ast.RShift)
ARITH = (ast.BinOp, ast.Compare, ast.AugAssign, ast.UnaryOp)
FMT_FIELD = re.compile(r"\{[^{}]*:[^{}]*?([A-Za-z])\}")
PCT = re.compile(r"%[-#0 +]*\d*(?:\.\d+)?([a-zA-Z])")


def load_policy(path=None):
    p = path or os.environ.get("DISCIPLINE_REPRLEAK") or (config.registers() / "reprleak.json")
    pol = dict(EMPTY)
    try:
        pol.update(json.loads(Path(p).read_text()))
    except (OSError, ValueError):
        pass
    pol["rules"] = dict(DEFAULT_RULES, **(pol.get("rules") or {}))
    for k in ("kernel", "constructors", "unwrap", "translations"):
        pol[k] = set(pol.get(k) or [])
    return pol


def _spec_of(fv):
    if fv.format_spec is None:
        return ""
    return "".join(v.value for v in fv.format_spec.values if isinstance(v, ast.Constant) and isinstance(v.value, str))


def _opts_in(src, tree, pol):
    """'marker' when the file carries or imports the kernel, 'pragma' when it only carries the pragma, else None."""
    oi = pol.get("opt_in") or {}
    if "class" in oi and any(isinstance(n, ast.ClassDef) and n.name == oi["class"] for n in tree.body):
        return "marker"
    if "import" in oi:
        for n in ast.walk(tree):
            if isinstance(n, ast.Import) and any(a.name.split(".")[0] == oi["import"] for a in n.names):
                return "marker"
            if isinstance(n, ast.ImportFrom) and (n.module or "").split(".")[0] == oi["import"]:
                return "marker"
    return "pragma" if PRAGMA_ON.search(src) else None


def check_file(path, pol):
    rows = []
    try:
        src = Path(path).read_text(errors="replace")
        tree = ast.parse(src)
    except (SyntaxError, ValueError):
        return rows
    how = _opts_in(src, tree, pol)
    if how is None:
        return rows
    rules, f = pol["rules"], Path(path).name
    display = {i + 1 for i, line in enumerate(src.splitlines()) if PRAGMA_DISPLAY.search(line)}
    exempt = set()
    for n in tree.body:
        if isinstance(n, (ast.FunctionDef, ast.ClassDef)) and n.name in pol["kernel"]:
            exempt.update(id(m) for m in ast.walk(n))
    parent = {}
    for node in ast.walk(tree):
        for ch in ast.iter_child_nodes(node):
            parent[id(ch)] = node
    bad_types = set("bo") | (set("xX") if rules["hex"] else set())
    via = (" (translations: %s)" % ", ".join(sorted(pol["translations"]))) if pol["translations"] else ""
    gate = False
    for node in ast.walk(tree):
        if id(node) in exempt:
            continue
        ln = getattr(node, "lineno", 1)
        if ln in display:
            continue
        if isinstance(node, ast.Call):
            fn = node.func
            name = fn.id if isinstance(fn, ast.Name) else (fn.attr if isinstance(fn, ast.Attribute) else None)
            if pol["gate"] and name == pol["gate"]:
                gate = True
            if rules["base"]:
                if isinstance(fn, ast.Name) and (fn.id in ("bin", "oct") or (fn.id == "hex" and rules["hex"])):
                    rows.append(("base-conversion", f, ln, "%s() reads a value through its storage%s" % (fn.id, via)))
                if isinstance(fn, ast.Name) and fn.id == "int" and len(node.args) >= 2:
                    b = node.args[1]
                    if isinstance(b, ast.Constant) and (b.value in (2, 8) or (b.value == 16 and rules["hex"])):
                        rows.append(("base-conversion", f, ln, "int(s, %r) parses a value through its storage" % b.value))
                if isinstance(fn, ast.Name) and fn.id == "format" and len(node.args) >= 2:
                    s = node.args[1]
                    if isinstance(s, ast.Constant) and isinstance(s.value, str) and s.value[-1:] in bad_types:
                        rows.append(("base-conversion", f, ln, "format(x, %r) prints through the storage" % s.value))
                if isinstance(fn, ast.Attribute) and fn.attr == "format" and isinstance(fn.value, ast.Constant) \
                        and isinstance(fn.value.value, str):
                    for m in FMT_FIELD.finditer(fn.value.value):
                        if m.group(1) in bad_types:
                            rows.append(("base-conversion", f, ln, "a str.format field of type %r prints through the"
                                                                     " storage" % m.group(1)))
            if rules["unwrap"] and isinstance(fn, ast.Attribute) and fn.attr in pol["unwrap"]:
                p = parent.get(id(node))
                if isinstance(p, ARITH) and not (isinstance(p, ast.BinOp) and isinstance(p.op, ast.Mod)
                                                 and isinstance(p.left, ast.Constant)):
                    rows.append(("unwrap", f, ln, "%s() feeds %s; a value moves only through a named translation%s"
                                 % (fn.attr, type(p).__name__, via)))
                if isinstance(p, ast.Call) and p is not node:
                    pn = p.func.id if isinstance(p.func, ast.Name) else (
                        p.func.attr if isinstance(p.func, ast.Attribute) else None)
                    if pn in pol["constructors"]:
                        rows.append(("unwrap", f, ln, "%s() feeds the constructor %s" % (fn.attr, pn)))
        elif rules["base"] and isinstance(node, ast.FormattedValue):
            spec = _spec_of(node)
            if spec[-1:] in bad_types:
                rows.append(("base-conversion", f, ln, "an f-string field of type %r prints through the storage"
                             % spec[-1:]))
        elif rules["base"] and isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod) \
                and isinstance(node.left, ast.Constant) and isinstance(node.left.value, str):
            for m in PCT.finditer(node.left.value):
                if m.group(1) in bad_types:
                    rows.append(("base-conversion", f, ln, "a %%-format of type %r prints through the storage"
                                 % m.group(1)))
        if rules["bitop"]:
            if isinstance(node, (ast.BinOp, ast.AugAssign)) and isinstance(node.op, BITOPS):
                rows.append(("raw-bitop", f, ln, "%s outside the kernel reads the storage" % type(node.op).__name__))
            elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Invert):
                rows.append(("raw-bitop", f, ln, "~ outside the kernel reads the storage"))
    if rules["gate"] and pol["gate"] and how == "marker" and not gate:
        rows.append(("no-gate", f, 1, "the file opts in and never calls %s" % pol["gate"]))
    return rows


def check(paths, pol=None):
    pol = pol or load_policy()
    rows, seen = [], set()
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(x for x in p.rglob("*.py") if not (set(x.parts) & config.SKIP))
        for x in files:
            if x.suffix != ".py" or x in seen:
                continue
            seen.add(x)
            rows += check_file(x, pol)
    for kind, f, i, d in rows:
        print(f"  {kind:<16} {f}:{i}  {d}")
    print(f"\n  reprleak: {len(rows)} rows")
    return rows


def _self_test():
    """A neutral kernel:  integers mod n wrapped in ModInt, one translation (lift), one gate (check_kernel)."""
    import tempfile
    d = Path(tempfile.mkdtemp())
    pol = load_policy(d / "absent.json")
    pol.update(opt_in={"class": "ModInt"}, kernel={"ModInt", "lift", "check_kernel"}, constructors={"ModInt"},
               unwrap={"as_int"}, gate="check_kernel", translations={"lift"})
    kern = ("class ModInt:\n    def __init__(self, v, n):\n        self.v, self.n = v % n, n\n"
            "    def as_int(self):\n        return self.v\n    def __xor__(self, o):\n        return self.v ^ o\n\n\n"
            "def lift(a, m):\n    return ModInt(a.v, m)\n\n\ndef check_kernel():\n    assert ModInt(5, 3).v == 2\n")
    probes = {
        "clean.py": kern + "\ncheck_kernel()\nx = lift(ModInt(4, 6), 3)\n",
        "base.py": kern + "\ncheck_kernel()\nprint(bin(ModInt(5, 7).as_int()))\n",
        "display.py": kern + "\ncheck_kernel()\nprint(hex(ModInt(5, 7).v))  # reprleak: display\n",
        "bitop.py": kern + "\ncheck_kernel()\ny = 5 ^ 3\n",
        "unwrap.py": kern + "\ncheck_kernel()\nz = ModInt(5, 7).as_int() + 1\n",
        "nogate.py": kern + "\nx = lift(ModInt(4, 6), 3)\n",
        "lookalike.py": "def lift(w, m):\n    return w << (m - 3)\n\nprint(lift(5, 8))\n",
        "pragma.py": "# reprleak: on\nprint(int('101', 2))\n",
    }
    for name, body in probes.items():
        (d / name).write_text(body)
    got = {name: [r[0] for r in check_file(d / name, pol)] for name in probes}
    assert got["clean.py"] == [], got
    assert got["base.py"] == ["base-conversion"], got
    assert got["display.py"] == [], got
    assert got["bitop.py"] == ["raw-bitop"], got
    assert got["unwrap.py"] == ["unwrap"], got
    assert got["nogate.py"] == ["no-gate"], got
    assert got["lookalike.py"] == [], got
    assert got["pragma.py"] == ["base-conversion"], got
    assert check_file(d / "base.py", load_policy(d / "absent.json")) == [], "an empty policy must read nothing"
    print("  self-test: the clean probe rows nothing;  base, bitop, unwrap and no-gate row once each, by kind;  a"
          " display line is skipped;  a file that only defines a kernel-like name is not read;  the pragma opts a file"
          " in;  an empty policy reads nothing.")
    return 0


if __name__ == "__main__":
    if "--self" in sys.argv:
        sys.exit(_self_test())
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
