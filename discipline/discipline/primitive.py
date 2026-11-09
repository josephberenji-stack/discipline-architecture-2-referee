"""
primitive.py -- the log space.  One verified instance, many carried copies, and a check
that every copy is still that instance.

WHY THIS EXISTS.  A claim-bearing file builds its own mathematics from the ground up
(ground.py).  That removes the silent shared premise and puts an equal and opposite risk in
its place: N copies of the same construction, drifting apart with nothing to say so.  The
answer is a log space: the mathematics is copied from one verified text, and every place
that carries a copy is known, so that a change to one copy is visible against the rest.

WHAT THE LOG SPACE IS.  primitives/<name>.py holds the canonical text of one function --
the thing to copy from.  registers/PRIMITIVES-REGISTER.md is generated and lists, for each
primitive, its hash, its library dependency if any, and every file carrying it with the
line it starts on.

WHAT IT CHECKS.  No markers are needed in the carrying files; identity is by name and
hash, so an edit cannot forget to update a marker.

  drift            a file defines a function whose NAME is registered and whose
                   normalised source hash is NOT the canonical one.  The two hashes are
                   printed.  Exact -- no tolerance, no window.
  unregistered     two or more files carry an identical function that the register does
                   not hold.  A duplicate nobody is watching.
  dead-primitive   a registered primitive that no file carries.
  stale-register   a list of carrying files that does not match what is on disk.

NORMALISATION.  ast.dump of the parsed function with docstrings blanked.  So a note added
to one copy's docstring is not drift; a changed constant, name, or operator is.  Comments
are not in the AST and are likewise not drift.

THE CANONICAL TEXT is the MAJORITY hash among the copies; a minority copy is a drift row.
Keying the register on (name, hash) instead would make two files carrying different
versions of one function into two separate primitives and nothing would row -- which is
exactly the failure the module exists to catch.

  python3 -m discipline.primitive --rebuild   regenerate the log space from the copies
                                              now on disk
  python3 -m discipline.primitive --rebuild-names A,B
                                              regenerate only the named primitives,
                                              keeping every other register section
  python3 -m discipline.primitive --self      the control

INDEPENDENT REIMPLEMENTATIONS.  registers/INDEPENDENT.md lists names two files implement
independently on purpose, each with a reason; a name there is exempt from the drift check.
A line with no reason is not an exemption.

Rows, not counts.
"""
import ast, hashlib, re, sys, collections
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

LIBS = ("numpy", "np", "scipy", "sympy", "sp")


def norm_hash(seg):
    t = ast.parse(seg)
    for n in ast.walk(t):
        if isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) \
           and isinstance(n.value.value, str):
            n.value.value = ""
    return hashlib.sha256(ast.dump(t).encode()).hexdigest()[:8]


def libs_used(seg):
    names = {n.id for n in ast.walk(ast.parse(seg)) if isinstance(n, ast.Name)}
    names |= {n.value.id for n in ast.walk(ast.parse(seg))
              if isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name)}
    return sorted(n for n in names if n in LIBS)


def top_functions(f):
    src = Path(f).read_text(errors="replace")
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return
    for n in tree.body:
        if isinstance(n, (ast.FunctionDef, ast.ClassDef)):     # a class copied between files is a primitive too
            seg = ast.get_source_segment(src, n)
            if seg and len(seg.splitlines()) >= 3:
                yield n.name, n.lineno, seg


def space_files(root):
    return sorted(f for f in Path(root).glob(config.glob_pattern()))


def load_independent(reg_dir):
    """Names two files implement independently on purpose, each with a reason.
    A line with no reason is not an exemption."""
    out, path = {}, Path(reg_dir) / "INDEPENDENT.md"
    if not path.is_file():
        return out
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith("#") or "|" not in line:
            continue
        name, _, reason = line.partition("|")
        name, reason = name.strip(), reason.strip()
        if name and reason:
            out[name] = reason
    return out


def load_register(reg_dir):
    """name -> dict(hash, libs, copies[(file, line)])"""
    reg, path = {}, Path(reg_dir) / "PRIMITIVES-REGISTER.md"
    if not path.is_file():
        return reg
    cur = None
    for line in path.read_text(errors="replace").splitlines():
        m = re.match(r"^## (\S+)\s+`([0-9a-f]{8})`(?:\s+lib:(\S+))?", line)
        if m:
            cur = m.group(1)
            reg[cur] = dict(hash=m.group(2),
                            libs=(m.group(3).split(",") if m.group(3) else []),
                            copies=[])
            continue
        m = re.match(r"^- (\S+):(\d+)\b", line)
        if m and cur:
            reg[cur]["copies"].append((m.group(1), int(m.group(2))))
    return reg


def rebuild(root=None, reg_dir=None, prim_dir=None):
    root = Path(root) if root else config.space()
    reg_dir = Path(reg_dir) if reg_dir else config.registers(root)
    prim_dir = Path(prim_dir) if prim_dir else root / "primitives"
    reg_dir.mkdir(exist_ok=True, parents=True)
    prim_dir.mkdir(exist_ok=True, parents=True)
    byname = collections.defaultdict(list)
    for f in space_files(root):
        if f.parent.name == "primitives":
            continue
        for name, ln, seg in top_functions(f):
            byname[name].append((f.name, ln, seg, norm_hash(seg)))
    out, kept = ["# PRIMITIVES-REGISTER -- the log space", "",
                 "Generated by `python3 -m discipline.primitive --rebuild`.  Never",
                 "hand-edited.  One section per primitive: its hash, the library it",
                 "needs if any, and every file carrying it.", ""], 0
    for name, copies in sorted(byname.items()):
        if len(copies) < 2:
            continue
        # the canonical text is the MAJORITY hash; a minority copy is drift and
        # the check says so, rather than the rebuild quietly making two buckets
        # of the same name.
        counts = collections.Counter(c[3] for c in copies)
        h = counts.most_common(1)[0][0]
        kept += 1
        seg = next(c[2] for c in copies if c[3] == h)
        libs = libs_used(seg)
        (prim_dir / f"{name}.py").write_text(
            f"# PRIMITIVE {name} @ {h}\n"
            f"# The canonical text.  Copy from here; never import from here.\n"
            f"# Carried by: {', '.join(c[0] for c in copies)}\n"
            + (f"# Needs: {', '.join(libs)}\n" if libs else "")
            + "\n" + seg.rstrip() + "\n")
        out.append(f"## {name}  `{h}`" + (f"  lib:{','.join(libs)}" if libs else ""))
        out.append("")
        for c, ln, _, ch in copies:
            out.append(f"- {c}:{ln}" + ("" if ch == h else f"   DRIFTED `{ch}`"))
        out.append("")
    (reg_dir / "PRIMITIVES-REGISTER.md").write_text("\n".join(out))
    drift = sum(1 for n, v in byname.items() if len(v) >= 2
                for c in v if c[3] != collections.Counter(
                    x[3] for x in v).most_common(1)[0][0])
    print(f"  register: {kept} primitives, "
          f"{sum(len(v) for n, v in byname.items() if len(v) >= 2)} carried copies, "
          f"{drift} of them drifted from the canonical text")
    return kept


_HEAD = ["# PRIMITIVES-REGISTER -- the log space", "",
         "Generated by `python3 -m discipline.primitive --rebuild`.  Never",
         "hand-edited.  One section per primitive: its hash, the library it",
         "needs if any, and every file carrying it.", ""]


def _write_primitive(prim_dir, name, copies):
    """write the canonical (majority-hash) text of one primitive; return its register section."""
    counts = collections.Counter(c[3] for c in copies)
    h = counts.most_common(1)[0][0]
    seg = next(c[2] for c in copies if c[3] == h)
    libs = libs_used(seg)
    (prim_dir / f"{name}.py").write_text(
        f"# PRIMITIVE {name} @ {h}\n"
        f"# The canonical text.  Copy from here; never import from here.\n"
        f"# Carried by: {', '.join(c[0] for c in copies)}\n"
        + (f"# Needs: {', '.join(libs)}\n" if libs else "")
        + "\n" + seg.rstrip() + "\n")
    sec = [f"## {name}  `{h}`" + (f"  lib:{','.join(libs)}" if libs else ""), ""]
    for c, ln, _, ch in copies:
        sec.append(f"- {c}:{ln}" + ("" if ch == h else f"   DRIFTED `{ch}`"))
    sec.append("")
    return sec


def rebuild_names(names, root=None, reg_dir=None, prim_dir=None):
    """regenerate only the named primitives; every other section of the register is kept as it stands.
    A full --rebuild regenerates every section from the copies on disk now, which drops a primitive whose copies
    have since moved out of the space; this one touches only what it is asked to."""
    root = Path(root) if root else config.space()
    reg_dir = Path(reg_dir) if reg_dir else config.registers(root)
    prim_dir = Path(prim_dir) if prim_dir else root / "primitives"
    reg_dir.mkdir(exist_ok=True, parents=True)
    prim_dir.mkdir(exist_ok=True, parents=True)
    want = set(names)
    byname = collections.defaultdict(list)
    for f in space_files(root):
        if f.parent.name == "primitives":
            continue
        for name, ln, seg in top_functions(f):
            if name in want:
                byname[name].append((f.name, ln, seg, norm_hash(seg)))
    path = reg_dir / "PRIMITIVES-REGISTER.md"
    text = path.read_text(errors="replace") if path.is_file() else ""
    head, sections, cur = [], {}, None
    for line in text.split("\n"):
        m = re.match(r"^## (\S+)", line)
        if m:
            cur = m.group(1)
            sections[cur] = [line]
        elif cur is None:
            head.append(line)
        else:
            sections[cur].append(line)
    if not any(head):
        head = list(_HEAD)
    done = 0
    for name in sorted(want):
        copies = byname.get(name, [])
        if len(copies) < 2:
            print(f"  {name}: carried by {len(copies)} file(s); a primitive needs two -- not registered"
                  + ("; its section is dropped" if name in sections else ""))
            sections.pop(name, None)
            continue
        sections[name] = _write_primitive(prim_dir, name, copies)
        done += 1
    body = []
    for name in sorted(sections):
        sec = sections[name]
        while sec and sec[-1] == "":
            sec = sec[:-1]
        body += sec + [""]
    while head and head[-1] == "":
        head = head[:-1]
    path.write_text("\n".join(head + [""] + body))
    print(f"  register: {done} named primitives regenerated, {len(sections)} sections in the register")
    return done


def check(paths, reg_dir=None):
    reg_dir = Path(reg_dir) if reg_dir else config.registers(paths[0] if paths else None)
    reg = load_register(reg_dir)
    indep = load_independent(reg_dir)
    rows = []
    if not reg:
        print("\n  primitive: 0 rows (no register; run --rebuild)")
        return rows
    on_disk = collections.defaultdict(list)
    unreg = collections.defaultdict(list)      # (name, hash) -> files, for names not registered
    scanned = set()
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(
            f for f in p.rglob("*.py") if not config.skipped(f))
        for f in files:
            if f in scanned:
                continue
            scanned.add(f)
            for name, ln, seg in top_functions(f):
                if name not in reg:
                    unreg[(name, norm_hash(seg))].append((str(f), ln))
                    continue
                h = norm_hash(seg)
                on_disk[name].append((f.name, ln))
                if h != reg[name]["hash"] and name not in indep:
                    rows.append(("drift", str(f), ln,
                                 f"'{name}' is {h}; the register holds "
                                 f"{reg[name]['hash']} (primitives/{name}.py)"))
    for (name, h), where in sorted(unreg.items()):
        if len({w for w, _ in where}) >= 2 and name not in indep:
            f0, ln0 = where[0]
            rows.append(("unregistered", f0, ln0,
                         f"'{name}' is carried identically by {len(where)} files "
                         f"({', '.join(Path(w).name for w, _ in where)}) and is not on the "
                         f"register -- a duplicate nobody is watching; run --rebuild"))
    for name, e in sorted(reg.items()):
        if not on_disk.get(name) and len(scanned) > 1:
            rows.append(("dead-primitive", f"primitives/{name}.py", 1,
                         "registered and carried by no file"))
        elif on_disk.get(name) and len(scanned) > 1:
            want = {c for c, _ in e["copies"]}
            got = {c for c, _ in on_disk[name]}
            if want != got:
                rows.append(("stale-register", f"{reg_dir.name}/PRIMITIVES-REGISTER.md", 1,
                             f"'{name}': register says {sorted(want)}, disk says "
                             f"{sorted(got)} -- run --rebuild"))
    for kind, f, i, d in rows:
        print(f"  {kind:<16} {f}:{i}  {d}")
    print(f"\n  primitive: {len(rows)} rows "
          f"({len(reg)} primitives registered, {len(indep)} names exempt as "
          f"declared-independent reimplementations)")
    return rows


def _self_test():
    import tempfile
    d = Path(tempfile.mkdtemp())
    body = "def twice(x):\n    y = x + x\n    return y\n"
    (d / "a.py").write_text(body)
    (d / "b.py").write_text(body)
    rebuild(d, d / "registers", d / "primitives")
    got = check([d], d / "registers")
    assert got == [], got
    (d / "b.py").write_text("def twice(x):\n    y = x * 2\n    return y\n")
    got = check([d], d / "registers")
    kinds = collections.Counter(r[0] for r in got)
    assert kinds["drift"] == 1, got
    thrice = "def thrice(x):\n    y = x + x\n    return y + x\n"
    (d / "c.py").write_text(thrice)
    (d / "e.py").write_text(thrice)
    got = check([d], d / "registers")
    kinds = collections.Counter(r[0] for r in got)
    assert kinds["unregistered"] == 1 and kinds["drift"] == 1, got
    klass = "class Pair:\n    def __init__(self, a, b):\n        self.a, self.b = a, b\n"
    (d / "f.py").write_text(klass)
    (d / "g.py").write_text(klass)
    got = check([d], d / "registers")
    assert any(r[0] == "unregistered" and "'Pair'" in r[3] for r in got), got
    assert rebuild_names(["Pair"], d, d / "registers", d / "primitives") == 1
    regtext = (d / "registers" / "PRIMITIVES-REGISTER.md").read_text()
    assert "## Pair" in regtext and "## twice" in regtext and "## thrice" not in regtext, regtext
    print("\n  self-test: two identical copies register and pass; changing one to "
          "x*2 rows as drift; an identical pair the register does not hold rows as "
          "unregistered; a copied class counts as a primitive; --rebuild-names adds "
          "only the named section and keeps the others.")
    return 0


if __name__ == "__main__":
    if "--self" in sys.argv:
        sys.exit(_self_test())
    if "--rebuild-names" in sys.argv:
        i = sys.argv.index("--rebuild-names")
        sys.exit(0 if rebuild_names(sys.argv[i + 1].split(",")) else 1)
    if "--rebuild" in sys.argv:
        sys.exit(0 if rebuild() else 1)
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
