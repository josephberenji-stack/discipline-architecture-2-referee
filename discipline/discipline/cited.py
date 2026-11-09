"""
cited.py -- a citation that nothing reads is decoration, and the item name is the address.

WHY THIS EXISTS.  When a result is cited, ask what it adds beyond the plain statement.  If
the argument survives deleting the citation, the citation was decoration and no dependency
was ever needed.  If it collapses, the dependency has to be exhibited.

  The index checks that every citation RESOLVES -- the file is there and the line is there.
  Nothing else checks that a citation DOES anything.  A requires-list entry that resolves
  and is never read passes every other check, and nothing on the page distinguishes it
  from one the file depends on.

WHAT IT CHECKS.  Every `requires=[...]` entry of every `declare()`.

  RESOLUTION.  "file.md:LINE label", "file.py:LINE", "file.out LABEL" and bare "file.out"
  are all accepted.  The file is found by name under the project roots (config.roots());
  the line is taken as given, or found from the label; the BLOCK at that line is the line
  plus what follows it up to the next header, because a citation that names a section
  header points at the section, not at the header text.

  LOAD-BEARING, three kinds, none of them a threshold:
    import        the cited module is imported by the citing file.
    runtime-read  the citing file opens the cited file while running.
    copy          the citing file contains >= COPY_RUN consecutive non-trivial lines
                  verbatim from the cited file, consecutive in BOTH files.  Load-bearing
                  for PROVENANCE, not for the argument: deleting the citation leaves the
                  argument standing and the borrowing unattributed.

  ROWS.
    no-such-file       the cited file is not under the project roots.
    label-not-at-line  a line and a PROSE label are given and the label is not in the block
                       at that line.  The citation resolves and points at the wrong place.
    item-not-anchored  a line and an ITEM NAME are given and the cited file does not anchor
                       that item at all -- no declare, no verdict, no printed head in a
                       .py; no bolded item header or item table row in a .md; no section
                       marker in an .out.  The citation has no address.
    line-stale         a line and an ITEM NAME are given, the file anchors the item, and
                       the line is not that item's own material.  The NAME is
                       authoritative and the LINE is advisory: the row carries the anchor
                       line to repair to, and is repairable without a human reading the
                       cited file.
    label-not-in-file  no line given, and the label is nowhere in the file.
    bare-file          neither line nor label: there is nothing to test.
    not-load-bearing   it resolves, the label is where it says, and the citing file has no
                       import, no runtime read and no copy.  Deleting this citation cannot
                       break the file.  The deletion test's decidable half; whether the
                       ARGUMENT survives is the half a parser cannot see, and the row is
                       where a human looks.
    prose-citation     it resolves and the label is where it says, and the cited file is a
                       .md or .out.  No prose citation can be an import, a runtime read or
                       a copy, so its outcome is forced by the citation's file type.
                       Reported apart from the row count so the headline is a measurement
                       and not a restatement of how many citations name prose.

WHAT IT DOES NOT CHECK.  Whether a not-load-bearing citation is decoration.  A theorem can
be the reason a computation is correct without being imported.  The row says the machine
cannot tell, not that the citation is wrong.  Token overlap between the citing file's code
and the cited block is deliberately not used: its answer moves with the window it is
measured in, and a threshold that can be tuned to any answer is not a measurement.  Only
the dependency tiers are reported, and they need no window.

ITEM NAMES.  An item is a short capitalised identifier of the form A1, BC3, DE12 -- one to
three capital letters followed by one to three digits, optionally primed.  A project that
names its items differently changes ITEMNAME and the anchor patterns here, in one place.

CONTROL.  `python3 -m discipline.cited --self` plants two citations in a scratch file: one
naming a module the file imports (must not row) and one naming a file it never touches
(must row).  Both are asserted.

Rows, not counts.
"""
import ast, os, re, sys, collections
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

COPY_RUN = 5
CITE = re.compile(r"^(?:.*/)?([^/:\s]+\.(?:py|md|out|lean|v))(?::(\d+))?(?:[\s,]+(.*))?$")
HEADER = re.compile(r'^\s*(print\(\s*f?["\']\s*[A-Z]|#{1,4} |\*\*[A-Z]|={8,}|-{8,})')
TRIVIAL = re.compile(r'^\s*(#|$|\)|\]|\}|else:|try:|pass$)')


def corpus_roots(start):
    """The project roots a citation may resolve into.  See config.roots()."""
    return config.roots(start)


def build_index(roots):
    idx = collections.defaultdict(list)
    for root in roots:
        for f in root.rglob("*"):
            if f.is_file() and f.suffix in config.INDEXED and not config.skipped(f):
                idx[f.name].append(f)
    for k in idx:
        idx[k].sort(key=lambda f: len(str(f)))
    return idx


def block_at(lines, ln, cap=45):
    out, i = [lines[ln - 1]], ln
    while i < len(lines) and len(out) < cap:
        if len(out) > 2 and HEADER.match(lines[i]):
            break
        out.append(lines[i]); i += 1
    return "\n".join(out)


STATUS = re.compile(r"\[(OPEN|PROVED|DEF|CITED|AXIOM|WITHDRAWN)\]", re.I)
ITEMNAME = re.compile(r"^[A-Z]{1,3}\d{1,3}[a-z′″\']?$")
VARPAT = re.compile(r"\b([a-z]{1,3}\d{1,3})_(?:bad|rows|ok|cnt|n|seen|hit)\b")
CALLPAT = re.compile(r"(?:declare|verdict|rows|control)\(\s*[\"\']([A-Za-z0-9_-]+)[\"\']")
HEADPAT = re.compile(r"print\(f?[\"\']\s*([A-Z]{1,3}\d{1,3}[a-z]?)[.:]")
MDHEAD = re.compile(r"^\*\*([A-Z]{1,3}\d{1,3}[a-z′″]?)\s*(?:—|--|-)\s")
MDROW = re.compile(r"^\|\s*\*\*([A-Z]{1,3}\d{1,3}[a-z′″]?)\*\*\s*\|")


def md_item(text):
    """the item a markdown line anchors, under either convention: a bolded section header
    `**X -- ` or a table row whose first cell is `**X**`."""
    m = MDHEAD.match(text) or MDROW.match(text)
    return m.group(1) if m else None
OUTMARK = re.compile(r"^\s*(?:\[([A-Z]{1,3}\d{1,3}[a-z]?)\]|([A-Z]{1,3}\d{1,3}[a-z]?)\.\s)")


def owner_map(lines):
    """each line takes the owner set of the smallest enclosing statement that has one."""
    out = {}
    try:
        tree = ast.parse("\n".join(lines))
    except SyntaxError:
        return out
    spans = []
    for node in ast.walk(tree):
        a = getattr(node, "lineno", None)
        b = getattr(node, "end_lineno", None)
        if a is None or b is None:
            continue
        text = "\n".join(lines[a - 1:b])
        own = set()
        for m in VARPAT.finditer(text):
            own.add(m.group(1).upper())
        for m in CALLPAT.finditer(text):
            if ITEMNAME.match(m.group(1)):
                own.add(m.group(1))
        for m in HEADPAT.finditer(text):
            own.add(m.group(1))
        if own:
            spans.append((b - a, a, b, frozenset(own)))
    spans.sort()
    for (_, a, b, own) in spans:
        for i in range(a, b + 1):
            out.setdefault(i, own)
    return out


def anchors(lines, item, suffix):
    """every line at which the item's own material begins in a file of this kind."""
    out = []
    if suffix == ".py":
        pats = [re.compile(r"declare\(\s*[\"\']" + re.escape(item) + r"[\"\']"),
                re.compile(r"verdict\(\s*[\"\']" + re.escape(item) + r"[\"\']"),
                re.compile(r"print\(f?[\"\']\s*" + re.escape(item) + r"[.:]")]
        for i, t in enumerate(lines):
            if any(p.search(t) for p in pats):
                out.append(i + 1)
        return out
    for i, t in enumerate(lines):
        tn = norm(t)
        if suffix == ".md":
            got = md_item(tn)
        else:
            m = OUTMARK.match(tn)
            got = (m.group(1) or m.group(2)) if m else None
        if got and norm(got) == norm(item):
            out.append(i + 1)
    return out


def all_anchors(lines, suffix):
    out = []
    for i, t in enumerate(lines):
        tn = norm(t)
        hit = md_item(tn) if suffix == ".md" else OUTMARK.match(tn)
        if hit:
            out.append(i + 1)
    return out


def owns_line(lines, item, suffix, ln):
    """does the cited line belong to the named item's own material?"""
    if suffix == ".py":
        return item in owner_map(lines).get(ln, frozenset())
    anc = anchors(lines, item, suffix)
    everything = all_anchors(lines, suffix)
    for a in anc:
        after = [x for x in everything if x > a]
        stop = min(after) if after else len(lines) + 1
        if a <= ln < stop:
            return True
    return False


def norm(t):
    """ASCII-fold primes and smart quotes so two spellings of one label are one label."""
    return (t.replace("″", "''").replace("′", "'")
             .replace("“", '"').replace("”", '"')
             .replace("‘", "'").replace("’", "'"))


def label_keys(label):
    """The locator tokens of a citation label, best first.  A status marker is not a
    locator: '[OPEN] the assignment lattice' locates by 'assignment', not by '[OPEN]'."""
    cleaned = STATUS.sub(" ", norm(label)).replace("/", " ")
    words = [w.strip("(),.:;") for w in cleaned.split()]
    words = [w for w in words if len(w) > 1 and w.lower() not in
             ("the", "a", "an", "of", "on", "in", "and", "its")]
    return words


def label_re(label):
    keys = label_keys(label)
    if not keys:
        return None
    return re.compile("|".join(r"(?<![A-Za-z0-9_])" + re.escape(k) + r"(?![A-Za-z0-9_])"
                               for k in keys))


def declares(tree, src):
    for n in ast.walk(tree):
        if isinstance(n, ast.Call) and (getattr(n.func, "attr", "") == "declare"
                                        or getattr(n.func, "id", "") == "declare"):
            claim = (n.args[0].value if n.args and isinstance(n.args[0], ast.Constant)
                     else "?")
            for kw in n.keywords:
                if kw.arg == "requires" and isinstance(kw.value, ast.List):
                    for e in kw.value.elts:
                        if isinstance(e, ast.Constant) and isinstance(e.value, str):
                            yield claim, e.value, getattr(e, "lineno", 0)


def imports_of(tree):
    got = set()
    for n in ast.walk(tree):
        if isinstance(n, ast.Import):
            for a in n.names:
                got.add(a.name.split(".")[0])
        elif isinstance(n, ast.ImportFrom) and n.module:
            got.add(n.module.split(".")[0])
    return got


def copies_from(src_lines, cited_lines):
    """>= COPY_RUN consecutive non-trivial lines that are consecutive in BOTH files.
    Membership alone is not a copy."""
    want = [l.rstrip() for l in cited_lines if not TRIVIAL.match(l)]
    mine = [l.rstrip() for l in src_lines if not TRIVIAL.match(l)]
    if len(want) < COPY_RUN or len(mine) < COPY_RUN:
        return False
    index = {}
    for i, l in enumerate(mine):
        index.setdefault(l, []).append(i)
    for j in range(len(want) - COPY_RUN + 1):
        for i in index.get(want[j], ()):
            if i + COPY_RUN > len(mine):
                continue
            if all(mine[i + k] == want[j + k] for k in range(COPY_RUN)):
                return True
    return False


def check(paths):
    rows, kinds, seen = [], collections.Counter(), collections.Counter()
    idx, roots = None, []
    for p in paths:
        p = Path(p)
        files = [p] if p.is_file() else sorted(f for f in p.rglob("*.py")
                                               if not config.skipped(f))
        for f in files:
            if idx is None:
                roots = corpus_roots(f)
                idx = build_index(roots)
            src = f.read_text(errors="replace")
            try:
                tree = ast.parse(src)
            except SyntaxError:
                continue
            src_lines = src.splitlines()
            imported = imports_of(tree)
            for claim, entry, at in declares(tree, src):
                m = CITE.match(entry.strip())
                if not m:
                    rows.append(("bare-file", str(f), at, claim, entry,
                                 "no file name in the citation")); continue
                base, line, label = m.group(1), m.group(2), (m.group(3) or "").strip()
                cands = idx.get(base, [])
                if not cands:
                    rows.append(("no-such-file", str(f), at, claim, entry,
                                 "no file of that name under " +
                                 ", ".join(r.name for r in roots))); continue
                cf = cands[0]
                seen["py" if cf.suffix == ".py" else "prose"] += 1
                clines = cf.read_text(errors="replace").splitlines()

                if line is None and not label:
                    rows.append(("bare-file", str(f), at, claim, entry,
                                 "names a file and nothing in it")); continue
                if line is not None:
                    ln = int(line)
                    if not 1 <= ln <= len(clines):
                        rows.append(("no-such-file", str(f), at, claim, entry,
                                     f"line {ln} past EOF ({len(clines)} lines)")); continue
                    item = label.split()[0] if label else ""
                    if label and ITEMNAME.match(norm(item)):
                        anc = anchors(clines, item, cf.suffix)
                        if not anc:
                            rows.append(("item-not-anchored", str(f), at, claim, entry,
                                         f"{cf.name} declares no item '{item}': the "
                                         f"citation has no address")); continue
                        if not owns_line(clines, item, cf.suffix, ln):
                            rows.append(("line-stale", str(f), at, claim, entry,
                                         f"'{item}' is anchored at {cf.name}:"
                                         f"{anc[0]}, not at :{ln} -- the name is the "
                                         f"address, the line is advisory"))
                            continue
                    elif label:
                        rx = label_re(label)
                        if rx and not rx.search(norm(block_at(clines, ln))):
                            rows.append(("label-not-at-line", str(f), at, claim, entry,
                                         f"'{label.split()[0]}' is not in the block at "
                                         f"{cf.name}:{ln}")); continue
                else:
                    rx = label_re(label)
                    if rx is None or not any(rx.search(norm(l)) for l in clines):
                        rows.append(("label-not-in-file", str(f), at, claim, entry,
                                     f"'{label}' is nowhere in {cf.name}")); continue

                if cf.suffix == ".py" and cf.stem in imported:
                    kinds["import"] += 1; continue
                if re.search(r'open\(\s*[^)]*' + re.escape(cf.name), src):
                    kinds["runtime-read"] += 1; continue
                if cf.suffix == ".py" and copies_from(src_lines, clines):
                    kinds["copy"] += 1; continue
                if cf.suffix != ".py":
                    rows.append(("prose-citation", str(f), at, claim, entry,
                                 "a .md/.out citation can never be an import or a "
                                 "copy: the deletion test has no mechanical purchase "
                                 "here and a human applies the rule"))
                    continue
                rows.append(("not-load-bearing", str(f), at, claim, entry,
                             "no import, no runtime read, no copy: deleting this "
                             "citation cannot break the file"))

    for kind, f, at, claim, entry, why in rows:
        print(f"  {kind:<18} {f}:{at}  [{claim}]  {entry}")
        print(f"  {'':<18}   {why}")
    tot = sum(kinds.values()) + len(rows)
    lb = sum(kinds.values())
    n_py = seen["py"]
    n_prose = tot - n_py
    prose_rows = sum(1 for r in rows if r[0] == "prose-citation")
    print("\n  load-bearing: " +
          (", ".join(f"{k} {v}" for k, v in sorted(kinds.items())) or "none"))
    print(f"  requires entries: {tot}.  {n_prose} name a .md or .out and CANNOT be an "
          f"import, a runtime read or a copy;")
    print(f"  that count is forced by the citation's file type and is not a "
          f"measurement.")
    print(f"  Of the {n_py} that name a .py, {lb} are load-bearing and "
          f"{n_py - lb} are not.")
    print(f"  cited: {len(rows)} rows ({len(rows) - prose_rows} on .py citations and "
          f"malformed ones, {prose_rows} prose)")
    return rows


def _self_test():
    import tempfile, textwrap
    d = Path(tempfile.mkdtemp()) / "project"
    d.mkdir(parents=True)
    (d / config.MARKER).write_text("")
    os.environ["DISCIPLINE_SPACE"] = str(d)
    os.environ.pop("DISCIPLINE_ROOTS", None)
    (d / "referee.py").write_text("def declare(*a, **k):\n    pass\n")
    (d / "faraway.py").write_text('print("P1.  A SECTION THIS FILE NEVER TOUCHES")\n'
                                  'X = 41\n')
    (d / "probe.py").write_text(textwrap.dedent('''\
        """probe."""
        import referee as R
        R.declare("C1", requires=["referee.py:1 declare"])
        R.declare("C2", requires=["faraway.py:1 P1"])
        '''))
    got = collections.Counter(r[0] for r in check([d / "probe.py"]))
    assert got["not-load-bearing"] == 1, got
    assert sum(got.values()) == 1, got
    print("\n  self-test: the imported citation does not row; the untouched one does.")
    return 0


if __name__ == "__main__":
    if "--self" in sys.argv:
        sys.exit(_self_test())
    sys.exit(1 if check(sys.argv[1:] or ["."]) else 0)
