"""referee_lean.py -- the driver of the Lean referee.

    python3 referee_lean.py --project=<lake project> --module=Path/To/Module.lean
    python3 referee_lean.py --project=<lake project> --modules=A.B,C.D [--scope-root=Pkg]
    python3 referee_lean.py --project=<lake project> --manifest=headlines.tsv [--mutate=L2,R1] [--with-L7]
    python3 referee_lean.py --project=<lake project> --selftest [--mutations]
    python3 referee_lean.py --project=<lake project> --modules=A.B --unfold-out=DIR     (also the unfold pass)
    python3 referee_lean.py --project=<lake project> --unfold-library=FILE              (the library's structures)
    python3 unfold_report.py --in=DIR [--library=FILE] --out=REPORT [--compare=OLD]     (UNFOLD-DESIGN.md)

It writes one check file (the imports of the modules, then RefereeCore.lean with the roots and registries of
registry.tsv filled in, then one `#referee` per theorem), compiles it with `lake env lean` inside the project, reads
the REFEREE lines, adds L4 (every backticked name of each module's header and every cited `File.lean:N` resolves),
and computes each theorem's class:
    D   L0 or L1 fails
    C   R3 fails (a registered open problem under hypotheses), or L2 finds an UNBUILT hypothesis;  C-vacuous if L3 fails
    RED L3 is REVIEW:  a reduction under a hypothesis refuted on file, used by another declaration;  the implication is the result
    B   R2 fails (an equivalence with an open problem)
    DEF R1 fails (structural)
    A?  everything passes:  REVIEW, never PASS -- novelty is decided by a person and a logged search;  an A? the
        manifest claims as B (known) is REVIEW too, held for a person's spot check of its `known as:` line, and FAIL
        when that line is empty or names no author and year.  A known result is not progress.
and compares it with the class the manifest claims.  A claim stronger than the computed class is FAIL.
Exit 1 on any FAIL, 2 on REVIEW only, 0 otherwise.

WHAT A PROJECT SUPPLIES, all in registry.tsv (or the file named by DISCIPLINE_LEAN_REGISTRY), one `kind<TAB>value`
per line, every kind empty in the release:
    root      a root namespace of the project's modules
    open      a registered open problem (a Lean constant):  R2, R3 and L3 measure against it
    target    a registered target statement:  R4 reports a binder-free theorem of that type as REVIEW
    claim     a word that, in a theorem's name, claims a target (R5);  `_proof_of_` and `solves` are built in
    carrier   a structure whose instances store propositions in their sections (R6)
    cite      a regular expression for a citation of the project's internal notes in a Lean file (L5)
    note      a regular expression for a non-library line, such as a ledger or session note (L6)
    data      a problem object (a Lean constant), the problem's own data:  circle gate Q1 and Q2 measure against it
    known     a theorem known to hold unconditionally (a Lean constant):  circle gate Q5, a label (KNOWN REVIEW)
    pin       a source file of a registered target, pinned:  `pin<TAB>path<TAB>sha256[<TAB>equivalence theorem]` (PIN)

The self-test runs the planted controls of controls/RefereeControls.lean and the expectations of controls.tsv, and
exits 1 when any control is not caught by its check or any positive control is flagged.  `--mutations` then runs
the self-test once with each check switched off and exits 1 unless every one of those runs fails:  each check is
shown to be the one that catches its control.
"""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKS = ["L0", "L1", "L1u", "L2", "L3", "L4", "L5", "L6", "LS", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "R1i", "DUP", "SHADOW", "INST", "VEND",
          "R1k", "UNFOLD", "BRIDGED", "CARRIER", "BEHAVE", "IFF", "IFFSET", "CARRY", "CIRCLE1", "CIRCLE2", "KNOWN", "CIRCLE", "PIN"]
# computed in Python over the unfold pass's lines (a whole package, or the self-test's check file), not per theorem in Lean
PACKAGE_CHECKS = ("UNFOLD", "BRIDGED", "CARRIER")
UNFOLD_OUT = None  # --unfold-out=DIR:  write each run's unfold lines there
# L7 (outside-library storage) ships off:  it states a project rule (objects are rebuilt, the outside library is a
# bridge) that not every project holds.  `--with-L7` turns it on.  A disabled check is not run and its controls are not
# expected.
DISABLED = ["L7"]
SCOPE_ROOT = None  # the package root imported for L2's inhabitant search (--scope-root=)
STRENGTH = {"D": 0, "C-vacuous": 0, "C": 1, "DEF": 1, "B": 2, "A?": 3, "A": 3}


KINDS = ("root", "open", "target", "claim", "carrier", "cite", "note", "data", "known", "pin")
REGISTRY = os.environ.get("DISCIPLINE_LEAN_REGISTRY") or os.path.join(HERE, "registry.tsv")


def registry(path=None):
    """the project's lists, by kind;  an unknown kind is an error, so a typo cannot silently empty a list."""
    reg = {k: [] for k in KINDS}
    for ln in open(path or REGISTRY, encoding="utf-8"):
        if ln.startswith("#") or not ln.strip():
            continue
        parts = ln.rstrip("\n").split("\t") + [""]
        kind, value = parts[0], ("\t".join(parts[1:]).strip("\t") if parts[0] == "pin" else parts[1])
        if kind not in reg:
            sys.exit(f"registry: unknown kind {kind!r} (known: {', '.join(KINDS)})")
        reg[kind].append(value.strip())
    return reg


def lean_list(xs):
    return "([" + ", ".join("`" + x for x in xs) + "] : List Name)"


def core_text(off):
    reg = registry()
    t = open(os.path.join(HERE, "RefereeCore.lean")).read()
    t = t.replace("@@ROOTS@@", lean_list(reg["root"])).replace("@@OPEN@@", lean_list(reg["open"]))
    t = t.replace("@@TARGETS@@", lean_list(reg["target"]))
    t = t.replace("@@DATA@@", lean_list(reg["data"])).replace("@@KNOWN@@", lean_list(reg["known"]))
    t = t.replace("@@OFF@@", "[" + ", ".join(f'"{c}"' for c in off) + "]")
    return t


def build_file(modules, body, names, off, extra_imports=(), header_tokens=None, storage=(), unfold=()):
    imports = "".join(f"import {m}\n" for m in list(extra_imports) + list(modules))
    core = core_text(off)
    core = core.split("import Lean\n", 1)
    # the step limit of the referee's own commands (found 3 Nov 2026 on the OAI Hodge closure:  `#referee_module` on
    # six groups of large HodgeConjecture modules stopped at Lean's default of 200000 heartbeats, after the modules
    # themselves had built);  finite, so a runaway check still stops;  REFEREE_HEARTBEATS overrides it (0 = no limit)
    hb = os.environ.get("REFEREE_HEARTBEATS", "4000000")
    text = (imports + "import Lean\n" + core[1] + "\n" + f"set_option maxHeartbeats {hb}\n" + body + "\n"
            + "".join(f"#referee {n}\n" for n in names))
    for m, toks in ({} if "L4" in off else (header_tokens or {})).items():
        text += f'#referee_resolve {m} "{" ".join(sorted(toks))}"\n'
    # L7:  the storage walk of each module (RefereeCore prints nothing when L7 is switched off)
    text += "".join(f"#referee_storage {m}\n" for m in storage)
    # the unfold pass (RefereeCore prints nothing when UNFOLD is switched off)
    text += "".join(f"#referee_unfold {m}\n" for m in unfold)
    return text


def unfold_lines(raw):
    """the unfold pass's machine lines, each a list of fields after `UNFOLD`."""
    out = []
    # printed on their own lines (IO.println), so they start the line;  a REFEREE row whose text contains the word
    # (the R1k kind UNFOLD) is not one
    for ln in raw.split("\n"):
        if ln.startswith("UNFOLD\t"):
            out.append(ln.rstrip("\n").split("\t")[1:])
    return out


def package_checks(ul, off, cover=()):
    """the checks read off the unfold lines of a whole package (or of the self-test's check file):
    UNFOLD   per scope (module or namespace):  the pass ran (SCHEMA and END lines), raised no ERROR, and gave every
             theorem it listed (and every name in `cover`) a THM line (PASS), else FAIL.
    BRIDGED  per theorem:  REVIEW when the theorem holds without content (R1k is not CONTENT) and its statement mentions
             a project type that carries an outside-library instance (an INSTOF line to a `mathlib` class):  the object
             is already bridged, and this law of it is proved by unfolding instead of through the bridge.  PASS for a
             structural theorem about no bridged type, INFO for a theorem that carries content.
    CARRIER  per project proposition used as a hypothesis:  REVIEW when theorems assume it and no theorem concludes it
             (it carries their hard part and is never established), PASS when some theorem concludes it."""
    rows = []
    thm = {f[1]: f for f in ul if f and f[0] == "THM" and len(f) >= 13}
    if "UNFOLD" not in off:
        scopes = {}
        for f in ul:
            if f and f[0] in ("SCHEMA", "END", "ERROR"):
                key = f[2] if f[0] == "SCHEMA" else f[1]
                scopes.setdefault(f[0], set()).add(key)
        decl_thms = {f[1] for f in ul if f and f[0] == "DECL" and len(f) > 2 and f[2] == "theorem"}
        missing = sorted((decl_thms | set(cover)) - set(thm))
        for s in sorted(scopes.get("SCHEMA", set())):
            bad = []
            if s not in scopes.get("END", set()):
                bad.append("no END line: the pass stopped")
            errs = [e for e in scopes.get("ERROR", set())]
            if errs:
                bad.append(f"{len(errs)} declarations raised errors ({errs[:3]})")
            if missing:
                bad.append(f"{len(missing)} theorems without a THM line ({missing[:4]})")
            rows.append(("UNFOLD", s, "FAIL" if bad else "PASS",
                         "; ".join(bad) if bad else f"{len(decl_thms)} theorems accounted for"))
    if "BRIDGED" not in off:
        bridged = {}
        for f in ul:
            if f and f[0] == "INSTOF" and len(f) >= 5 and f[3] == "mathlib":
                for ty in f[4].split(","):
                    if ty and ty != "-":
                        bridged.setdefault(ty, set()).add(f[2])
        for n, f in sorted(thm.items()):
            tys = [x for x in f[12].split(",") if x in bridged]
            if f[2] == "CONTENT":
                rows.append(("BRIDGED", n, "INFO", "carries content"))
            elif tys:
                rows.append(("BRIDGED", n, "REVIEW", f"{f[2]}: a law of {tys[:3]}, which carry {sorted(bridged[tys[0]])[:3]}; "
                                                     "proved by unfolding, not through the bridge"))
            else:
                rows.append(("BRIDGED", n, "PASS", f"{f[2]}: no bridged object in the statement"))
    if "CARRIER" not in off:
        assumed, concluded = {}, set()
        for n, f in thm.items():
            hs = [h for h in f[5].split(",") if h and h != "-"]
            for h in hs:
                assumed.setdefault(h, []).append(n)
            # established:  concluded by a theorem that does not assume it (P n from P m is a transport, not a proof)
            if f[11] != "-" and f[11] not in hs:
                concluded.add(f[11])
        for p, users in sorted(assumed.items()):
            if p in concluded:
                rows.append(("CARRIER", p, "PASS", f"assumed by {len(users)} theorems, established on file"))
            else:
                rows.append(("CARRIER", p, "REVIEW", f"assumed by {len(users)} theorems ({sorted(users)[:3]}), "
                                                     "established by none: it carries their hard part"))
    return rows


def run_lean(project, text):
    fd, path = tempfile.mkstemp(suffix=".lean", dir=project)
    with os.fdopen(fd, "w") as f:
        f.write(text)
    try:
        # one Lean process, capped (REFEREE_MEM MB, default 6144):  several uncapped ones can exhaust a machine
        p = subprocess.run(["lake", "env", "lean", f"-M{os.environ.get('REFEREE_MEM', '6144')}", "-j2",
                            os.path.basename(path)], cwd=project, capture_output=True, text=True)
    finally:
        os.unlink(path)
    out = p.stdout + p.stderr
    rows, names = [], {}
    for ln in out.split("\n"):
        i = ln.find("REFEREE\t")
        if i >= 0:
            parts = ln[i:].split("\t")
            if len(parts) >= 5:
                rows.append(tuple(parts[1:5]))
        j = ln.find("REFEREE_NAMES\t")
        if j >= 0:
            _, m, ns = (ln[j:].split("\t") + [""])[:3]
            names[m] = set(ns.split())
    errs = [ln for ln in out.split("\n") if ": error" in ln]
    if p.returncode != 0 and not errs:
        # a Lean process that dies (out of memory, a crash) prints no `: error` line;  without this its run would
        # report no rows and pass
        last = [ln for ln in out.split("\n") if ln.strip()][-1:] or ["no output"]
        errs = [f"lean exited {p.returncode}: {last[0][:200]}"]
    return rows, names, errs, out


def header_of(src):
    """the module's doc header:  the comment that opens the file, and the Mathlib-layout module docstring `/-! … -/`,
    which L6 asks to come after the imports.  Both are read:  a file opening on `import` has its header after them."""
    parts = []
    if src.lstrip().startswith("/-"):
        parts.append(src.split("-/", 1)[0])
    m = re.search(r"/-!(.*?)-/", src, re.S)
    if m:
        parts.append(m.group(1))
    return "\n".join(parts)


_SRC_ROOTS = {}


def src_path(project, m):
    """the source file of module `m`:  under the project, else under the folder below it that holds the module's first
    component (a Lake `srcDir`, as in the OAI Hodge closure, 2 Nov 2026:  `HodgeConjecture` sat below the project
    folder, and every group's class step stopped on FileNotFoundError after Lean had run).  The folder found is kept
    for the run.  None when no file is found."""
    rel = m.replace(".", "/") + ".lean"
    first = m.split(".")[0]
    for root in [project, _SRC_ROOTS.get((project, first))]:
        if root and os.path.exists(os.path.join(root, rel)):
            return os.path.join(root, rel)
    for dirpath, dirnames, _ in os.walk(project):
        dirnames[:] = [d for d in dirnames if not d.startswith(".") and d not in ("build", "lake-packages")]
        if dirpath[len(project):].count(os.sep) > 3:
            dirnames[:] = []
            continue
        if os.path.exists(os.path.join(dirpath, rel)):
            _SRC_ROOTS[(project, first)] = dirpath
            return os.path.join(dirpath, rel)
    return None


def missing_sources(project, mods):
    """SRC:  every module named has a source file;  checked before Lean runs, so a wrong project folder stops at once."""
    gone = [m for m in mods if src_path(project, m) is None]
    for m in gone:
        print(f"REFEREE\tSRC\t{m}\tFAIL\tno source file for the module under {project} (looked to depth 3)")
    return gone


def header_tokens_of(src):
    head = header_of(src)
    return {t for t in re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)`", head) if not t.endswith(".lean") and "/" not in t}


def l4(project, modules, names):
    rows = []
    for m in modules:
        path = src_path(project, m)
        if path is None:
            rows.append(("L4", m, "FAIL", "module file not found"))
            continue
        src = open(path, encoding="utf-8", errors="replace").read()
        head = header_of(src)
        missing = []
        badref = []
        # a citation `Some/File.lean:12` (or `:12, 40`) in the header, read relative to the project
        for pth, lines in re.findall(r"([\w./-]+?\.lean):((?::?\d+,?\s*)+)", head):
            real = os.path.join(project, pth)
            if not os.path.exists(real):
                badref.append(f"{pth} (no such file)")
                continue
            n = sum(1 for _ in open(real, errors="replace"))
            for k in re.findall(r"\d+", lines):
                if int(k) > n:
                    badref.append(f"{pth}:{k} (file has {n} lines)")
        st = "PASS" if not badref else "FAIL"
        det = "every cited path:line exists" if st == "PASS" else f"bad citations {badref[:5]}"
        rows.append(("L4m", m, st, det))
    return rows


# the rows printed once per module, never read as a theorem's rows
MODULE_ROWS = ("L7", "L7obj")


HEAD_NAME = re.compile(r"(^|_)(top|global|master|universal|main)(_|$)", re.I)


def claim_name():
    words = ["_proof_of_", "solves"] + [re.escape(w) for w in registry()["claim"] if w]
    return re.compile("(" + "|".join(words) + ")", re.I)


def prop_carriers(src):
    """names of instances of a registered carrier whose sections are propositions:  `def X … : C where` with a field
    `… := PLift (…)`, C a `carrier` of the registry."""
    out = set()
    for c in registry()["carrier"]:
        pat = r"def\s+(\S+)[^\n]*:\s*(?:\S*\.)?" + re.escape(c) + r"\s+where\s*\n((?:\s+.*\n){1,4})"
        for m in re.finditer(pat, src):
            if re.search(r":=\s*PLift\b", m.group(2)):
                out.add(m.group(1).split(".")[-1])
    return out


def statement(src, short):
    m = re.search(r"theorem\s+(?:\S+\.)?" + re.escape(short) + r"\b(.*?):=", src, re.S)
    return m.group(1) if m else ""


def static_rows(thm, src, lean_rows, off):
    """R5 (names) and R6 (target in the sections), read from the source and from the Lean rows."""
    short = thm.split(".")[-1]
    rows = []
    st = {c: s_ for c, _, s_, _ in lean_rows}
    if "R5" not in off:
        if claim_name().search(short):
            if st.get("R4") == "REVIEW" and st.get("L0") == "PASS":
                rows.append(("R5", thm, "REVIEW", "a target name on a theorem that typechecks as the target statement: a person confirms"))
            else:
                rows.append(("R5", thm, "FAIL", "the name claims a target result its statement does not state"))
        elif HEAD_NAME.search(short) and (st.get("R1") == "FAIL" or st.get("R7") == "REVIEW"):
            rows.append(("R5", thm, "REVIEW", "a headline name over a structural or packaged proof: report it with that class beside it"))
        else:
            rows.append(("R5", thm, "PASS", "the name claims nothing beyond the statement"))
    if "R6" not in off:
        pp = prop_carriers(src)
        hit = [x for x in pp if re.search(r"\b" + re.escape(x) + r"\b", statement(src, short))]
        if hit:
            rows.append(("R6", thm, "FAIL", f"states a property of {hit}, whose sections are propositions: the target sits in the sections"))
        else:
            rows.append(("R6", thm, "PASS", "no proposition-section carrier in the statement"))
    if "CIRCLE" not in off:
        rows.append(circle_row(thm, lean_rows))
    return rows


def circle_row(thm, lean_rows):
    """The circle gate (project-record/clay/CIRCLE-GATE.md, Q1–Q6), one row per theorem from the rows already made:
    Q1 CIRCLE1, Q2 CIRCLE2, Q3 R1 (agreement by unfolding) or DUP (the same definition under two names), Q4 R2 (an
    iff with an open side), Q5 KNOWN.  One "yes" on Q1–Q4:  FAIL, the step circles (class CIRCLE).  Only Q5:  REVIEW,
    "unconditional, not a step toward the target".  Otherwise PASS, with Q6 asked of the person:  name the one new
    statement."""
    st = {c: s_ for c, _, s_, _ in lean_rows}
    yes = [q for q, hit in (("Q1", st.get("CIRCLE1") == "FAIL"), ("Q2", st.get("CIRCLE2") == "FAIL"),
                            ("Q3", st.get("R1") == "FAIL" or st.get("DUP") in ("REVIEW", "FAIL")),
                            ("Q4", st.get("R2") == "FAIL")) if hit]
    if yes:
        return ("CIRCLE", thm, "FAIL", f"circles on {yes}: true, but it carries no information about the problem")
    if st.get("KNOWN") == "REVIEW":
        return ("CIRCLE", thm, "REVIEW", "unconditional (Q5): a native build, not a step toward the target")
    return ("CIRCLE", thm, "PASS", "passes Q1–Q4; Q6: name the one new statement it makes")


def pin_rows(pins, base, label=None):
    """E1, source pinning of a registered target (9 Nov 2026):  each `pin` is a source file with the sha256 it was
    pinned at.  Unchanged:  PASS.  Changed with an equivalence theorem named on the pin:  REVIEW (a person confirms
    that theorem states the equivalence and passes the referee).  Changed with none:  FAIL, the target moved."""
    import hashlib
    rows = []
    for i, p in enumerate(pins):
        f = (p.split("\t") + ["", ""])[:3]
        path, want, bridge = f[0].strip(), f[1].strip(), f[2].strip()
        full = path if os.path.isabs(path) else os.path.join(base, path)
        name = (label[i] if label else path)
        if not os.path.exists(full):
            rows.append(("PIN", name, "FAIL", f"{path}: the pinned file is missing"))
            continue
        got = hashlib.sha256(open(full, "rb").read()).hexdigest()
        if got == want:
            rows.append(("PIN", name, "PASS", f"{path}: unchanged since pinning ({want[:12]})"))
        elif bridge:
            rows.append(("PIN", name, "REVIEW", f"{path}: changed ({want[:12]} -> {got[:12]}); equivalence named: {bridge}; a person confirms it"))
        else:
            rows.append(("PIN", name, "FAIL", f"{path}: changed since pinning ({want[:12]} -> {got[:12]}) with no equivalence to the pinned version"))
    return rows


_DECL_INDEX = {}


def decl_index(project):
    """last name component -> files declaring it, over every .lean of the project (built once)."""
    if project in _DECL_INDEX:
        return _DECL_INDEX[project]
    idx, mods = {}, set()
    for root, dirs, files in os.walk(project):
        if ".lake" in root.split(os.sep):
            continue
        for f in files:
            if f.endswith(".lean"):
                mods.add(f[:-5])
                path = os.path.join(root, f)
                for m in re.finditer(r"^\s*(?:private |protected |noncomputable |partial )*(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)",
                                     open(path, encoding="utf-8", errors="replace").read(), re.M):
                    idx.setdefault(m.group(1).split(".")[-1], set()).add(os.path.relpath(path, project))
    _DECL_INDEX[project] = (idx, mods)
    return idx, mods


def refine_l4(project, row):
    """an L4 FAIL from Lean lists names not in the imported environment.  A name declared in another file of the
    project is REVIEW (cited but not imported);  a module or file name is accepted;  a name declared nowhere is FAIL."""
    m = re.search(r"\[(.*)\]", row[3])
    if row[2] != "FAIL" or not m:
        return row
    idx, mods = decl_index(project)
    nowhere, elsewhere = [], []
    for t in [x.strip() for x in m.group(1).split(",") if x.strip()]:
        last = t.split(".")[-1]
        if t in mods or last in mods or re.search(r"\.(out|md|py|tsv|lean|log)$", t):
            continue
        if last in idx:
            elsewhere.append(f"{t} ({sorted(idx[last])[0]})")
        else:
            nowhere.append(t)
    if nowhere:
        return (row[0], row[1], "FAIL", f"header names declared nowhere in the project: {nowhere}" +
                (f"; cited but not imported: {elsewhere}" if elsewhere else ""))
    if elsewhere:
        return (row[0], row[1], "REVIEW", f"header names declared in files this module does not import: {elsewhere}")
    return (row[0], row[1], "PASS", "header names resolve to modules, files or declarations")


# built in:  a quotation or provenance note (L5), and ledger or session notes (L6);  a project adds its own patterns
# as `cite` and `note` rows of the registry
CITE_BUILTIN = [r"\bverbatim\s*[:(]", r"^\s*#*\s*Provenance\b"]
NOTE_BUILTIN = [r"^\s*(LEDGER|SESSION NOTES?)\b", r"\bthread\b", r"\bqueue row\b"]


def thesis_cite():
    return re.compile("|".join(CITE_BUILTIN + [p for p in registry()["cite"] if p]), re.I)


def not_library():
    return re.compile("|".join(NOTE_BUILTIN + [p for p in registry()["note"] if p]))


def l6(name, src):
    """L6:  the Mathlib layout.  The module docstring `/-! ... -/` comes after the imports and has `# Title` and
    `## Main results`;  the file carries no ledger, session or thread notes;  every public `theorem`, `def`,
    `structure`, `class` and `instance` that is not `private` has a `/-- ... -/` docstring."""
    bad = []
    m = re.search(r"/-!(.*?)-/", src, re.S)
    if not m:
        bad.append("no module docstring /-! … -/")
    else:
        doc = m.group(1)
        if not re.search(r"^\s*#\s+\S", doc, re.M):
            bad.append("module docstring has no `# Title`")
        if not re.search(r"^\s*##\s+Main (results|statements|definitions)", doc, re.M):
            bad.append("module docstring has no `## Main results`")
        if src.find("/-!") < src.rfind("\nimport "):
            bad.append("module docstring above an import")
    nl = not_library()
    notes = [i + 1 for i, ln in enumerate(src.split("\n")) if nl.search(ln)]
    if notes:
        bad.append(f"{len(notes)} non-library lines (ledger, thread or session notes; lines {notes[:5]})")
    undoc = []
    lines = src.split("\n")
    # a line that starts inside a comment is no declaration (`/-! … theorem `x` … -/` prose)
    in_comment, depth = [], 0
    for ln in lines:
        in_comment.append(depth > 0)
        depth = max(0, depth + len(re.findall(r"/-", ln)) - len(re.findall(r"-/", ln)))
    for i, ln in enumerate(lines):
        if in_comment[i]:
            continue
        # an attribute may sit on the declaration's own line (`@[simp] theorem …`)
        mm = re.match(r"(?:@\[[^\]]*\]\s*)*(?:noncomputable |protected )*(theorem|lemma|def|abbrev|structure|class|inductive)"
                      r"\s+([^\s:]+)", ln)
        if mm:
            j = i - 1
            # lines holding only an attribute, and blank lines, may sit between the docstring and the declaration;  an `open … in` or
            # `set_option … in` line may not (a docstring above it does not parse), so it is not skipped
            while j >= 0 and (re.match(r"\s*@\[[^\]]*\]\s*$", lines[j]) or lines[j].strip() == ""):
                j -= 1
            ok = False
            if j >= 0 and lines[j].rstrip().endswith("-/"):
                # the comment that ends on line j must itself be a docstring:  find where it opens
                k = j
                while k >= 0 and "/-" not in lines[k].replace("-/", ""):
                    k -= 1
                ok = k >= 0 and "/--" in lines[k]
            if not ok:
                undoc.append(mm.group(2))
    if undoc:
        bad.append(f"{len(undoc)} public declarations without a docstring ({undoc[:4]})")
    return ("L6", name, "FAIL" if bad else "PASS", "; ".join(bad) if bad else "Mathlib layout; every public declaration documented")
LEAN_REL = re.compile(r"[↔→∀∃=≤<≥>∣∈¬∧∨⊆]|:\s*\S")


# L4 on a module that opens on `import` (its header is the docstring after the imports):  one whose backticked
# names all exist, and one naming a declaration that exists nowhere.
IMPORT_DOC_GOOD = """import Mathlib.Data.Nat.Basic

/-!
# Successor bounds

## Main results

* `Nat.succ_le_of_lt`, `Nat.le_refl`: the two facts used; no `native_decide` (a tactic, read as syntax).
-/
"""
IMPORT_DOC_BAD = IMPORT_DOC_GOOD.replace("`Nat.le_refl`", "`no_such_declaration_q7`")

# L7:  the namespaces of the storage controls in controls/RefereeControls.lean (each starts with `Referee`, so the
# self-test runs no `#referee` on it)
STORAGE_CONTROLS = ["RefereeStorageDirect", "RefereeStorageThrough", "RefereeStorageProofOnly", "RefereeStorageClean",
                    "Bridge.RefereeStorageBridged", "RefereeStorageReadsBridge"]


GOOD_DOC = """import Mathlib.Data.Nat.Basic

/-!
# The descent bound

## Main results

* `good_bound`: every natural number is at least zero.

## References

* L. J. Mordell, 1922.
-/

/-- Every natural number is at least zero. -/
theorem good_bound (n : ℕ) : 0 ≤ n := Nat.zero_le n
"""


INST_PAT = re.compile(r"attribute\s*\[\s*(-instance|local instance|scoped instance)|^\s*local instance\b|^\s*attribute\s*\[local\b", re.M)


def inst(name, src):
    """INST:  a module that removes an instance or adds a local one changes what notation means for the declarations
    after it, so a statement and its proof may read one symbol through two structures (REVIEW)."""
    hits = [str(src[:m.start()].count("\n") + 1) for m in INST_PAT.finditer(src)]
    if hits:
        return ("INST", name, "REVIEW", f"instance changes at lines {', '.join(hits[:8])}")
    return ("INST", name, "PASS", "no instance changes")


def vend(name, relpath):
    """VEND:  a project module stored under a `Mathlib` folder of the project is a vendored copy of library code; which
    copy a name means then depends on the import order (REVIEW)."""
    parts = relpath.replace("\\", "/").split("/")
    if "Mathlib" in parts[:-1] and not name.startswith("Mathlib."):
        return ("VEND", name, "REVIEW", f"vendored library path {relpath}")
    return ("VEND", name, "PASS", "not under a Mathlib folder")


def l5(name, src):
    """L5:  a Lean file is written as a mathematical library.  It cites none of the project's internal notes and
    quotes no one, and every [OPEN] item states the missing result as a Lean statement in backticks (an expression
    with a relation, a quantifier or a type ascription), not as prose."""
    tc = thesis_cite()
    cites = [i + 1 for i, ln in enumerate(src.split("\n")) if tc.search(ln)]
    lines = src.split("\n")
    vague = []
    for i, ln in enumerate(lines):
        if "[OPEN]" not in ln:
            continue
        j = i
        while j > 0 and i - j < 8 and not re.match(r"\s*(\(\d+\)|\d+\.|\(\w\)|[A-Z]{2,}[^a-z]{0,20}[.:])", lines[j]):
            j -= 1
        item = " ".join(lines[j:i + 1])
        if not any(LEAN_REL.search(b) for b in re.findall(r"`([^`]+)`", item)):
            vague.append(i + 1)
    bad = []
    if cites:
        bad.append(f"{len(cites)} citations of internal notes or quotations (lines {cites[:6]})")
    if vague:
        bad.append(f"{len(vague)} [OPEN] items with no Lean statement in backticks (lines {vague[:6]})")
    return ("L5", name, "FAIL" if bad else "PASS", "; ".join(bad) if bad else "no internal citation; every [OPEN] item is stated in Lean")


def classify(thm_rows):
    st = {c: s for c, _, s, _ in thm_rows}
    det = {c: d for c, _, _, d in thm_rows}
    if st.get("L0") == "FAIL" or st.get("L1") == "FAIL":
        return "D"
    if st.get("L3") == "FAIL":
        return "C-vacuous"
    if st.get("L3") == "REVIEW":
        return "RED"
    # C from the status and the explicit count, not from the row text (a long hypothesis may be cut in the text)
    m = re.search(r"unbuilt=(\d+)", det.get("L2", ""))
    unbuilt = int(m.group(1)) if m else (1 if "UNBUILT" in det.get("L2", "") else 0)
    if st.get("R3") == "FAIL" or (st.get("L2") == "FAIL" and (unbuilt > 0 or not m)):
        return "C"
    if st.get("R2") == "FAIL" or st.get("R6") == "FAIL":
        return "B"
    if st.get("R5") == "FAIL":
        return "D"
    if st.get("R1") == "FAIL":
        return "DEF"
    if st.get("CIRCLE") == "FAIL":
        return "CIRCLE"
    return "A?"


KNOWN_YEAR = re.compile(r"\b(1[5-9]\d\d|20\d\d)\b")


def known_line_problem(known):
    """Why a manifest's `known as:` entry is not well formed, or None when it is:  it must be non-empty, must not
    read "none found" (a claim of class B names the theorem it matches), and must name an author and a year."""
    k = (known or "").strip()
    if not k or k == "-":
        return "no known-as entry: a known-or-restatement claim carries a `known as:` line naming the theorem"
    if k.lower().startswith("none found"):
        return "the known-as entry reads 'none found', which contradicts a claim of class B"
    if not KNOWN_YEAR.search(k) or not re.search(r"[A-Za-z]{3,}", k):
        return f"the known-as entry `{k}` names no author and year"
    return None


def claimed_b_status(known):
    """The status of a theorem the checks class A? and the manifest claims as B (known):  held as REVIEW for a
    person's spot check of the known-as line, or FAIL when that line is malformed."""
    bad = known_line_problem(known)
    if bad:
        return "FAIL", bad
    return "REVIEW", (f"known as: {known.strip()}; held for a person's spot check of the known-as line;  class B is not "
                      "progress")


def status_selftest():
    """The Python-level test of claimed_b_status (no Lean).  Exit 1 when any expectation fails."""
    cases = [("", "FAIL"), ("-", "FAIL"), ("none found (queries x; 25 Oct 2026)", "FAIL"), ("standard", "FAIL"),
             ("elementary", "FAIL"), ("Baer, the structure of divisible groups, 1940", "REVIEW"),
             ("Smith normal form (Smith 1861)", "REVIEW"), ("Perron 1907, Frobenius 1912", "REVIEW")]
    bad = 0
    for known, want in cases:
        got, why = claimed_b_status(known)
        ok = got == want
        bad += not ok
        print(f"STATUS_SELFTEST\t{'ok' if ok else 'FAIL'}\t{known!r}\t{got}\t{why}")
    print(f"STATUS_SELFTEST\t{len(cases) - bad} of {len(cases)} as expected")
    return 1 if bad else 0


def report(project, manifest, off):
    entries = []
    for ln in open(manifest):
        if ln.startswith("#") or not ln.strip():
            continue
        f = ln.rstrip("\n").split("\t")
        entries.append(dict(thm=f[0], module=f[1], claimed=f[2], known=f[3] if len(f) > 3 else ""))
    mods = sorted({e["module"] for e in entries})
    if missing_sources(project, mods):
        return 1
    toks = {m: header_tokens_of(open(src_path(project, m), encoding="utf-8",
                                       errors="replace").read()) for m in mods}
    rows, names, errs, raw = run_lean(project, build_file(mods, "", [e["thm"] for e in entries], off, header_tokens=toks,
                                                          storage=mods))
    if errs:
        print("REFEREE\tBUILD\t-\tFAIL\t" + " | ".join(errs[:5]))
        return 1
    rows = [refine_l4(project, r) if r[0] == "L4" else r for r in rows]
    rows += l4(project, mods, names)
    if "L5" not in off:
        for m in mods:
            srcm = open(src_path(project, m), encoding="utf-8", errors="replace").read()
            rows.append(l5(m, srcm))
            if "L6" not in off:
                rows.append(l6(m, srcm))
    for m in mods:
        srcm = open(src_path(project, m), encoding="utf-8", errors="replace").read()
        if "INST" not in off:
            rows.append(inst(m, srcm))
        if "VEND" not in off:
            rows.append(vend(m, m.replace(".", "/") + ".lean"))
    worst = 0
    for e in entries:
        mine = [r for r in rows if r[1].endswith(e["thm"]) and r[0] not in MODULE_ROWS]
        src = open(src_path(project, e["module"]), encoding="utf-8", errors="replace").read()
        mine += static_rows(e["thm"], src, mine, off)
        for r in mine:
            print("REFEREE\t" + "\t".join(r))
        cls = classify(mine)
        claimed = e["claimed"]
        ran = {r[0] for r in mine}
        missing_checks = [c for c in ["L0", "L1", "L2", "L3", "R1", "R2", "R3", "R4", "R7"] if c not in off and c not in ran]
        if missing_checks:
            print(f"REFEREE\tCLASS\t{e['thm']}\tFAIL\tthe Lean checks {missing_checks} printed nothing: the referee did not run on it")
            worst = 3
            continue
        if claimed == "-":
            hard = [r for r in mine if r[0] in ("L0", "L1", "L3", "R5") and r[2] == "FAIL"]
            status = "FAIL" if hard else ("REVIEW" if cls in ("A?",) or any(r[2] == "REVIEW" for r in mine) else "PASS")
            why = f"computed class {cls}" + (f"; broken: {[r[0] for r in hard]}" if hard else "")
            print(f"REFEREE\tCLASS\t{e['thm']}\t{status}\t{why}")
            worst = max(worst, {"PASS": 0, "REVIEW": 2, "FAIL": 3}[status])
            continue
        if cls == "D":
            status, why = "FAIL", f"claimed {claimed}, computed D: broken (an extra axiom, a stand-in, or a name that claims more than the proof); fix it before it is reported"
        elif cls == "A?":
            status, why = "REVIEW", "no mechanical objection; novelty needs a person and a logged search"
            if claimed == "B":
                status, why = claimed_b_status(e["known"])
        elif STRENGTH.get(claimed, 3) > STRENGTH[cls]:
            status, why = "FAIL", f"claimed {claimed}, computed {cls}"
        else:
            status, why = "PASS", f"claimed {claimed}, computed {cls}"
        if any(r[2] == "REVIEW" for r in mine) and status == "PASS":
            status, why = "REVIEW", why + "; a check asks for a person"
        print(f"REFEREE\tCLASS\t{e['thm']}\t{status}\t{why}")
        worst = max(worst, {"PASS": 0, "REVIEW": 2, "FAIL": 3}[status])
    for r in rows:
        if r[0] in ("L4", "L4m", "L5", "L6", "L7", "L7obj", "INST", "VEND"):
            print("REFEREE\t" + "\t".join(r))
            if r[2] == "FAIL":
                worst = 3
            elif r[0] in ("L7", "INST", "VEND") and r[2] == "REVIEW":
                worst = max(worst, 2)
    return {0: 0, 2: 2, 3: 1}[worst]


def report_modules(project, mods, off):
    """every theorem of each module, found in the compiled environment (`#referee_module`);  no claimed class:  the
    class each theorem computes, and FAIL only on what is broken in any class."""
    if missing_sources(project, mods):
        return 1
    toks = {m: header_tokens_of(open(src_path(project, m), encoding="utf-8",
                                       errors="replace").read()) for m in mods}
    # L2 scope:  with `--scope-root=<module>` the check file also imports that module (the package root), so an
    # inhabitant of a hypothesis built anywhere in the package is found;  the theorems checked are still only those of
    # the modules named
    extra = [SCOPE_ROOT] if SCOPE_ROOT else []
    text = build_file(mods, "", [], off, extra_imports=extra, header_tokens=toks, storage=mods,
                      unfold=mods if UNFOLD_OUT else ()) + "".join(f"#referee_module {m}\n" for m in mods)
    rows, names, errs, raw = run_lean(project, text)
    if UNFOLD_OUT:
        os.makedirs(UNFOLD_OUT, exist_ok=True)
        # the file name joins the modules;  past the file system's name limit (255 bytes) it is the first module, the
        # count of the others and a hash of the whole list (found on the OAI Hodge closure, 1 Nov 2026:  groups of 25
        # HodgeConjecture modules stopped on OSError 36 before any row was written)
        name = "+".join(mods)
        if len(name.encode()) > 200:
            import hashlib
            name = f"{mods[0]}+{len(mods) - 1}-more-{hashlib.sha1(name.encode()).hexdigest()[:12]}"
        with open(os.path.join(UNFOLD_OUT, name + ".unfold.tsv"), "w") as f:
            for u in unfold_lines(raw):
                f.write("\t".join(u) + "\n")
    if errs:
        print("REFEREE\tBUILD\t-\tFAIL\t" + " | ".join(errs[:5]))
        return 1
    rows = [refine_l4(project, r) if r[0] == "L4" else r for r in rows]
    worst = 0
    by = {}
    for r in rows:
        if r[0] not in ("L4", "MODULE") + MODULE_ROWS:
            by.setdefault(r[1], []).append(r)
    for thm, mine in by.items():
        mod = next((m for m in mods if thm.startswith(m + ".") or thm.startswith(m.rsplit(".", 1)[0])), mods[0])
        src = open(src_path(project, mod), encoding="utf-8", errors="replace").read()
        mine += static_rows(thm, src, mine, off)
        for r in mine:
            print("REFEREE\t" + "\t".join(r))
        cls = classify(mine)
        hard = [r[0] for r in mine if r[0] in ("L0", "L1", "L3", "R5") and r[2] == "FAIL"]
        status = "FAIL" if hard else ("REVIEW" if cls == "A?" or any(r[2] == "REVIEW" for r in mine) else "PASS")
        print(f"REFEREE\tCLASS\t{thm}\t{status}\tcomputed class {cls}" + (f"; broken: {hard}" if hard else ""))
        worst = max(worst, {"PASS": 0, "REVIEW": 2, "FAIL": 3}[status])
    for r in rows:
        if r[0] in ("L4", "MODULE") + MODULE_ROWS:
            print("REFEREE\t" + "\t".join(r))
            if r[0] == "L7" and r[2] == "FAIL":
                worst = 3
            elif r[0] == "L7" and r[2] == "REVIEW":
                worst = max(worst, 2)
    for m in mods:
        srcm = open(src_path(project, m), encoding="utf-8", errors="replace").read()
        mrows = [l5(m, srcm), l6(m, srcm)]
        if "INST" not in off:
            mrows.append(inst(m, srcm))
        if "VEND" not in off:
            mrows.append(vend(m, m.replace(".", "/") + ".lean"))
        for row in mrows:
            print("REFEREE\t" + "\t".join(row))
            if row[2] == "FAIL":
                worst = max(worst, 3)
            elif row[0] in ("INST", "VEND") and row[2] == "REVIEW":
                worst = max(worst, 2)
    return {0: 0, 2: 2, 3: 1}[worst]


def strip_block_comments(src):
    """the source with every block comment (`/- … -/`, nested, docstrings included) blanked to spaces, newlines kept:
    a comment line that starts with `end` or `theorem` is no scope and no theorem."""
    out, depth, i, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth += 1
            out.append("  ")
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            out.append("  ")
            i += 2
        else:
            c = src[i]
            out.append(c if depth == 0 or c == "\n" else " ")
            i += 1
    return "".join(out)


def module_manifest(project, path):
    """every theorem of one module, with no claimed class:  the referee then reports the class it computes and fails
    only on what is broken in any class (L0, L1, L3, L4, R5)."""
    src = open(os.path.join(project, path), encoding="utf-8", errors="replace").read()
    mod = path[:-5].replace("/", ".")
    # one stack of open scopes:  a namespace adds its name to the prefix, a section (named or not) or a `mutual`
    # block adds nothing, and `end` closes the innermost scope of either kind (`end torus` closes `section torus`,
    # not the namespace around it)
    scopes = []
    names = []
    for ln in strip_block_comments(src).split("\n"):
        m = re.match(r"namespace\s+(\S+)", ln)
        if m:
            scopes.append(m.group(1))
        elif re.match(r"(?:(?:noncomputable|public|private)\s+)*section\b", ln) or re.match(r"mutual\s*$", ln):
            scopes.append(None)
        elif re.match(r"end\b", ln) and scopes:
            scopes.pop()
        m = re.match(r"(?:private |protected )?theorem\s+(\S+)", ln)
        if m:
            names.append(".".join([s for s in scopes if s] + [m.group(1)]))
    fd, tmp = tempfile.mkstemp(suffix=".tsv")
    with os.fdopen(fd, "w") as f:
        for n in names:
            f.write(f"{n}\t{mod}\t-\t\n")
    return tmp


# LS:  names the skip filter must check (a person's theorem whose name begins `eq_`) and names it must skip (what the
# compiler writes);  the names need not exist
SKIP_CONTROLS = {"RefereeControls.eq_of_x": "PASS", "RefereeControls.ctrlFun.eq_1": "INFO",
                 "RefereeControls.ctrlFun.eq_def": "INFO", "RefereeControls.ctrlFun.match_1": "INFO",
                 "RefereeControls.ctrlFun.match_1_1": "INFO", "Nat.brecOn": "INFO", "RefereeControls.match_up": "PASS",
                 "RefereeControls.controlled_x": "PASS", "RefereeControls.CtrlPt.ext": "INFO",
                 "RefereeControls.CtrlPt.ext_iff": "INFO", "RefereeControls.CtrlColour.ofNat_ctorIdx": "INFO"}


def selftest(project, off, quiet=False, rows_out=None):
    """the planted controls, against their own registry (controls/registry-selftest.tsv), never the project's."""
    global REGISTRY
    saved, REGISTRY = REGISTRY, os.path.join(HERE, "controls", "registry-selftest.tsv")
    try:
        return _selftest(project, off, quiet, rows_out)
    finally:
        REGISTRY = saved


def _selftest(project, off, quiet=False, rows_out=None):
    ctrl = open(os.path.join(HERE, "controls", "RefereeControls.lean")).read()
    expect = []
    for ln in open(os.path.join(HERE, "controls", "controls.tsv")):
        if ln.startswith("#") or not ln.strip():
            continue
        thm, check, status = ln.rstrip("\n").split("\t")[:3]
        expect.append((thm, check, status))
    thms = sorted({t for t, c, _ in expect if c != "LS" and c != "BEHAVE" and c not in PACKAGE_CHECKS})
    body = ctrl
    text = build_file([], body, ["RefereeControls." + t for t in thms if not t.startswith("Referee")], off,
                      extra_imports=["Mathlib.NumberTheory.LSeries.RiemannZeta", "Mathlib.Data.ZMod.Basic"],
                      header_tokens={"RefereeControls": header_tokens_of(ctrl),
                                     "RefereeImportGood": header_tokens_of(IMPORT_DOC_GOOD),
                                     "RefereeImportBad": header_tokens_of(IMPORT_DOC_BAD)},
                      storage=STORAGE_CONTROLS, unfold=["RefereeControls"])
    text += "".join(f"#referee_skip {n}\n" for n in SKIP_CONTROLS)
    rows, _, errs, raw = run_lean(project, text)
    errs = [e for e in errs if "declaration uses 'sorry'" not in e]
    bad = 0
    if errs:
        print("SELFTEST\tthe control file does not compile:", " | ".join(errs[:5]))
        return 1
    for t in thms:
        if t.startswith("Referee"):
            continue
        mine = [r for r in rows if r[1].split(".")[-1] == t]
        rows += static_rows("RefereeControls." + t, ctrl, mine, off)
        # the computed class, so a control can expect a class
        mine = [r for r in rows if r[1].split(".")[-1] == t]
        rows.append(("CLASS", "RefereeControls." + t, classify(mine), "computed class"))
    if "L5" not in off:
        rows.append(l5("RefereeControls", ctrl))
        good = ('/-\n  The descent bound for y^2 = x^3 + D.  Known as: Mordell (1922).\n'
                '  (1) The image sizes:  `∀ D : ℤ, D ≠ 0 → Nat.card (alphaHom D).range ≤ 3 ^ 2`.  [OPEN]\n-/\n')
        rows.append(l5("RefereeGoodDoc", good))
        quote = GOOD_DOC.replace("## References", "## Provenance\n\nA. Person, 1 Oct 2026, verbatim:  \"a quote\".\n\n## References")
        rows.append(l5("RefereeQuote", quote))
    if "L6" not in off:
        rows.append(l6("RefereeControls", ctrl))
        rows.append(l6("RefereeGoodDoc", GOOD_DOC))
    if "INST" not in off:
        rows.append(inst("RefereeInstBad", "import Mathlib.Data.Nat.Basic\nattribute [-instance] Nat.instDvdNat\n"))
        rows.append(inst("RefereeInstGood", GOOD_DOC))
    if "VEND" not in off:
        rows.append(vend("RefereeVendored", "Proj/Mathlib/Algebra/Group/Basic.lean"))
        rows.append(vend("RefereeNotVendored", "Proj/Base/Group.lean"))
    if "PIN" not in off:
        import hashlib
        fd, pinned = tempfile.mkstemp(suffix=".lean")
        os.close(fd)
        try:
            with open(pinned, "w") as f:
                f.write("theorem pinned_target : True := trivial\n")
            h = hashlib.sha256(open(pinned, "rb").read()).hexdigest()
            rows += pin_rows([f"{pinned}\t{h}", f"{pinned}\t{'0' * 64}", f"{pinned}\t{'0' * 64}\tRefereeControls.ctrl_circle_dep"],
                             "/", label=["RefereePinGood", "RefereePinMoved", "RefereePinBridged"])
        finally:
            os.remove(pinned)
    rows += package_checks(unfold_lines(raw), off,
                           cover=["RefereeControls." + t for t in thms if not t.startswith("Referee")])
    if "BEHAVE" not in off:
        rows += behave_selftest(project)
    if rows_out is not None:
        rows_out.extend(rows)
        with open(os.path.join(HERE, "selftest-rows.tsv"), "w") as f:
            for r in rows:
                f.write("\t".join(r) + "\n")
    return evaluate(rows, expect, off, quiet)


BEHAVE_PLANT = """
namespace RefereeBehaveSelftest
/-- multiplication written out by recursion (the behaviour step's self-test row). -/
def mulOut : Nat → Nat → Nat
  | _, 0 => 0
  | n, m + 1 => mulOut n m + n
end RefereeBehaveSelftest
"""


def behave_selftest(project):
    """the behaviour step (BEHAVIOUR-DESIGN.md control 6):  the planted `mulOut` scored on `HMul.hMul` must be a
    candidate (S >= 0.8 on at least 3 laws, values agreeing), and on `Nat.add` must not.  With the step off there are
    no rows, and the self-test fails."""
    import behaviour_run as BRUN
    import behaviour_report as BREP
    fd, raw = tempfile.mkstemp(suffix=".raw")
    os.close(fd)
    try:
        text = BRUN.check_file([], ["#referee_behave_pairs RefereeBehaveSelftest.mulOut HMul.hMul "
                                    "RefereeBehaveSelftest.mulOut Nat.add"]).replace(
            "set_option maxHeartbeats 0", BEHAVE_PLANT + "\nset_option maxHeartbeats 0", 1)
        errs = BRUN.run(project, text, raw)
        got = BREP.pair_scores(raw)
    finally:
        for f in (raw, raw + ".log"):
            if os.path.exists(f):
                os.unlink(f)
    if errs:
        return [("BEHAVE", "RefereeBehaveSelftest.behave_mul", "FAIL", "the check file failed: " + errs[0][:120])]
    m = got.get(("RefereeBehaveSelftest.mulOut", "HMul.hMul"))
    a = got.get(("RefereeBehaveSelftest.mulOut", "Nat.add"))
    return [("BEHAVE", "RefereeBehaveSelftest.behave_mul", "PASS" if m and BREP.is_candidate(*m[:3]) else "FAIL",
             f"mulOut on HMul.hMul: {m}"),
            ("BEHAVE", "RefereeBehaveSelftest.behave_add", "PASS" if a and not BREP.is_candidate(*a[:3]) else "FAIL",
             f"mulOut on Nat.add: {a}")]


def evaluate(rows, expect, off, quiet):
    bad = 0
    got = {(r[1].split(".")[-1], r[0]): r[2] for r in rows}
    expect = [e for e in expect if e[1] not in DISABLED]
    for thm, check, status in expect:
        g = got.get((thm, check))
        ok = g == status
        bad += not ok
        if not quiet or not ok:
            print(f"SELFTEST\t{thm}\t{check}\texpected {status}\tgot {g}\t{'ok' if ok else 'NOT CAUGHT'}")
    print(f"SELFTEST\t{len(expect) - bad} of {len(expect)} expectations met" + (f" (checks off: {off})" if off else ""))
    return 1 if bad else 0


def main(argv):
    global SCOPE_ROOT, UNFOLD_OUT
    project, manifest, off, st, muts, sig = None, None, list(DISABLED), False, False, []
    modules, library, library_imports = None, None, ["Mathlib"]
    decode_library, decode_out, decode_modules = None, None, None
    for a in argv:
        if a.startswith("--scope-root="):
            SCOPE_ROOT = a.split("=", 1)[1]
            continue
        if a.startswith("--unfold-out="):
            UNFOLD_OUT = a.split("=", 1)[1]
            continue
        if a.startswith("--unfold-library="):
            library = a.split("=", 1)[1]
            continue
        if a.startswith("--decode-library="):
            decode_library = a.split("=", 1)[1]
            continue
        if a.startswith("--decode-out="):
            decode_out = a.split("=", 1)[1]
            continue
        if a.startswith("--decode-modules="):
            decode_modules = a.split("=", 1)[1].split(",")
            continue
        if a.startswith("--library-imports="):
            # what the library dump imports (default the whole of Mathlib)
            library_imports = a.split("=", 1)[1].split(",")
            continue
        if a.startswith("--project="):
            project = a.split("=", 1)[1]
        elif a.startswith("--manifest="):
            manifest = a.split("=", 1)[1]
        elif a.startswith("--modules="):
            # acted on after every option is read (an option after it, such as --unfold-out, must still count)
            modules = a.split("=", 1)[1].split(",")
        elif a.startswith("--module="):
            manifest = module_manifest(project, a.split("=", 1)[1])
        elif a.startswith("--mutate="):
            off = list(DISABLED) + a.split("=", 1)[1].split(",")
        elif a == "--with-L7":
            DISABLED.remove("L7")
            off = [c for c in off if c != "L7"]
        elif a.startswith("--signature="):
            sig = a.split("=", 1)[1].split(",")
        elif a == "--selftest":
            st = True
        elif a == "--status-selftest":
            return status_selftest()
        elif a == "--mutations":
            muts = True
    if decode_library or (decode_out and decode_modules):
        # the decode step (DECODE-DESIGN.md):  the library's MDECL lines, or the DDECL lines of the named modules
        if decode_library:
            text = ("".join(f"import {m}\n" for m in library_imports) + "import Lean\n"
                    + core_text(off).split("import Lean\n", 1)[1] + "\n#referee_decode_library\n")
            target = decode_library
        else:
            planted = open(os.path.join(HERE, "controls", "DecodeControls.lean")).read()
            text = (build_file(decode_modules, planted, [], off) + "".join(f"#referee_decode {m}\n" for m in decode_modules)
                    + "#referee_decode RefereeDecodeControls\n")
            target = decode_out
        rows, _, errs, raw = run_lean(project, text)
        n = 0
        with open(target, "w") as f:
            for u in unfold_lines(raw):
                f.write("\t".join(u) + "\n")
                n += 1
        print(f"DECODE\t{n} lines\t{target}")
        if errs:
            print("DECODE\terrors: " + " | ".join(errs[:5]))
            return 1
        return 0
    if library:
        # every structure and class of the outside library, for the counterparts report
        rows, _, errs, raw = run_lean(project, "".join(f"import {m}\n" for m in library_imports) + "import Lean\n"
                                      + core_text(off).split("import Lean\n", 1)[1]
                                      + "\n#referee_unfold_library\n")
        with open(library, "w") as f:
            for u in unfold_lines(raw):
                f.write("\t".join(u) + "\n")
        if errs:
            print("UNFOLD_LIBRARY\terrors: " + " | ".join(errs[:5]))
            return 1
        return 0
    if (modules or manifest) and "PIN" not in off:
        # E1:  the registered targets' pinned sources, checked before the theorems
        for r in pin_rows(registry()["pin"], project):
            print("REFEREE\t" + "\t".join(r))
    if modules:
        return report_modules(project, modules, off)
    if sig:
        text = build_file(sig, "", [], off) + "".join(f"#referee_signature {m}\n" for m in sig)
        rows, _, errs, raw = run_lean(project, text)
        lines = sorted(ln[ln.find("REFEREE_SIG"):] for ln in raw.split("\n") if "REFEREE_SIG" in ln)
        print("\n".join(lines))
        if errs:
            print("SIGNATURE\terrors: " + " | ".join(errs[:5]))
            return 1
        return 0
    if st:
        rc = selftest(project, off)
        if rc or not muts:
            return rc
        survived = []
        for c in CHECKS:
            print(f"MUTATION\tswitching off {c}")
            if selftest(project, [c] + DISABLED, quiet=True) == 0:
                survived.append(c)
        if survived:
            print(f"MUTATION\tFAIL: the self-test still passed with {survived} off; those checks catch nothing")
            return 1
        print(f"MUTATION\tevery check is needed: the self-test fails with any one of {CHECKS} off")
        return 0
    return report(project, manifest, off)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
