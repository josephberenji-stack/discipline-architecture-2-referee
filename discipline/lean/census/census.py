"""census.py -- the kernel census:  what the source states, what the kernel accepted, and what the referee classed.

    python3 census.py --project=<lake project> --modules=A.B,C.D --out=DIR [--referee-log=FILE]
    python3 census.py --selftest

The referee walks the constants a module declares and decides which of them are a person's theorems.  A checker can
be blind:  a filter that skips too much leaves theorems no check ever reads, and nothing in the referee's own output
says so.  The census closes that loop by comparing three lists that are made independently:

  stated     the declarations the source text names (a plain scan of each module file, comments removed);
  accepted   every constant the kernel holds for each module, with its kind, read from the compiled environment by a
             generated Lean file (nothing is written into the project but that file, which is deleted after the run);
  classed    the theorems the referee printed a CLASS row for (from `referee_lean.py --modules=... > FILE`).

It writes, in DIR:
  accepted-constants.tsv        module, kind, origin (gen: compiler-generated; proj: a structure projection; user), name
  stated-vs-accepted.tsv        per module:  stated, accepted, and the two differences
  gaps.tsv                      each stated-not-accepted and accepted-not-stated name
  name-shapes.tsv               the accepted theorems by the shape of their last name component (`eq_<n>`, `eq_def`,
                                `match_<n>`, ...), the table a toolchain change is checked against
  accepted-not-classed.tsv      (with --referee-log) accepted user theorems with no CLASS row:  the referee's blind spot

A difference is not an error by itself:  generated names are expected in `accepted-not-stated`.  The file to read is
`accepted-not-classed.tsv`:  every row there is a theorem the kernel accepted and no check read.  On a new toolchain,
rerun the census and compare `name-shapes.tsv` before trusting the referee's skip list.
"""
import collections, os, re, subprocess, sys, tempfile

ACCEPTED_LEAN = r"""
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let wanted : List Name := @@MODULES@@
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless wanted.contains m do continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let gen := n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n || Lean.Meta.isMatcherCore env n
    let origin := if gen then "gen" else if env.isProjectionFn n then "proj" else "user"
    IO.println s!"ACC\t{m}\t{kind}\t{origin}\t{n}"
"""

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|example)\b\s*(\S*)")
# the shapes of the last name component Lean 4.33.1 writes for a declaration (the referee skips the first five)
SHAPES = [("eq_<n>", re.compile(r"eq_\d+$")), ("eq_def", re.compile(r"eq_def$")), ("match_<n>", re.compile(r"match_\d+$")),
          ("sizeOf_spec", re.compile(r"sizeOf_spec$")), ("congr_simp", re.compile(r"congr_simp$")),
          ("inj / injEq", re.compile(r"inj(Eq)?$")), ("eq_ (a person's name)", re.compile(r"eq_\D"))]


def strip_comments(src):
    src = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), src, flags=re.S)
    return "\n".join(ln.split("--")[0] for ln in src.split("\n"))


def stated_names(src):
    """the declarations a module's text names, with their namespaces;  `example` and anonymous instances are not names."""
    ns, out = [], {}
    for ln in strip_comments(src).split("\n"):
        m = re.match(r"\s*namespace\s+(\S+)", ln)
        if m:
            ns.append(m.group(1)); continue
        if re.match(r"\s*section\b", ln):
            ns.append(None); continue
        if re.match(r"\s*end\b", ln) and ns:
            ns.pop(); continue
        m = DECL.match(ln)
        if m:
            k, nm = m.group(1), m.group(2)
            if k == "example" or (k == "instance" and (not nm or nm[0] in "([{:")):
                continue
            full = nm[7:] if nm.startswith("_root_.") else ".".join([x for x in ns if x] + [nm])
            out[full] = k
    return out


def compare(stated, accepted):
    """stated: {module: {name: kind}};  accepted: {module: [(kind, gen, name)]}.  Returns rows and gaps."""
    rows, gaps = [], []
    for m in sorted(set(stated) | set(accepted)):
        st = stated.get(m, {})
        user = {n: k for k, g, n in accepted.get(m, []) if g == "user"}
        gen = [n for k, g, n in accepted.get(m, []) if g == "gen"]

        def found(full):
            return full in user or any(u.endswith("." + full) for u in user)

        sset = set(st)

        def is_stated(u):
            return u in sset or any(u.endswith("." + s) for s in sset)

        missing = [n for n in st if not found(n)]
        extra = [u for u in user if not is_stated(u)]
        rows.append((m, len(st), sum(1 for v in st.values() if v in ("theorem", "lemma")), len(user),
                     sum(1 for v in user.values() if v == "theorem"), len(gen), len(missing), len(extra)))
        gaps += [(m, "stated-not-accepted", st[n], n) for n in missing]
        gaps += [(m, "accepted-not-stated", user[u], u) for u in extra]
    return rows, gaps


def classed_names(log):
    out = set()
    for ln in open(log, encoding="utf-8", errors="replace"):
        p = ln.rstrip("\n").split("\t")
        if len(p) >= 4 and p[0] == "REFEREE" and p[1] == "CLASS":
            out.add(p[2])
    return out


def shape_of(name):
    last = name.split(".")[-1]
    for label, pat in SHAPES:
        if pat.match(last):
            return label
    return "other"


def not_classed(accepted, classed):
    """accepted user theorems the referee printed no CLASS row for, by shape (a generated shape is expected here)."""
    out = []
    for m, lst in accepted.items():
        for k, g, n in lst:
            if k == "theorem" and g == "user" and n not in classed and not any(c.endswith("." + n) for c in classed):
                out.append((m, shape_of(n), n))
    return out


def run(project, modules, outdir, log=None):
    text = "".join(f"import {m}\n" for m in modules) + ACCEPTED_LEAN.replace(
        "@@MODULES@@", "([" + ", ".join("`" + m for m in modules) + "] : List Name)")
    fd, path = tempfile.mkstemp(suffix=".lean", dir=project)
    with os.fdopen(fd, "w") as f:
        f.write(text)
    try:
        p = subprocess.run(["lake", "env", "lean", f"-M{os.environ.get('REFEREE_MEM', '6144')}", "-j2",
                            os.path.basename(path)], cwd=project, capture_output=True, text=True)
    finally:
        os.unlink(path)
    errs = [ln for ln in (p.stdout + p.stderr).split("\n") if ": error" in ln]
    if errs:
        print("CENSUS\tBUILD\tFAIL\t" + " | ".join(errs[:5]))
        return 1
    accepted = collections.defaultdict(list)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "accepted-constants.tsv"), "w") as o:
        o.write("module\tkind\torigin\tname\n")
        acc_rows = sorted(tuple(ln[ln.find("ACC\t"):].split("\t")[1:5]) for ln in p.stdout.split("\n") if "ACC\t" in ln)
        for m, k, g, n in acc_rows:
            accepted[m].append((k, g, n))
            o.write(f"{m}\t{k}\t{g}\t{n}\n")
    stated = {m: stated_names(open(os.path.join(project, m.replace(".", "/") + ".lean"), encoding="utf-8",
                                   errors="replace").read()) for m in modules}
    rows, gaps = compare(stated, accepted)
    with open(os.path.join(outdir, "stated-vs-accepted.tsv"), "w") as o:
        o.write("module\tstated\tstated_theorems\taccepted_user\taccepted_theorems\taccepted_generated"
                "\tstated_not_accepted\taccepted_not_stated\n")
        for r in rows:
            o.write("\t".join(map(str, r)) + "\n")
    with open(os.path.join(outdir, "gaps.tsv"), "w") as o:
        o.write("module\tgap\tkind\tname\n")
        for g in gaps:
            o.write("\t".join(g) + "\n")
    shapes = collections.Counter(shape_of(n) for lst in accepted.values() for k, g, n in lst if k == "theorem")
    with open(os.path.join(outdir, "name-shapes.tsv"), "w") as o:
        o.write("shape\taccepted_theorems\n")
        for s, c in shapes.most_common():
            o.write(f"{s}\t{c}\n")
    t = [sum(r[i] for r in rows) for i in range(1, 8)]
    print(f"CENSUS\tstated {t[0]}\tstated theorems {t[1]}\taccepted user {t[2]}\taccepted theorems {t[3]}"
          f"\tgenerated {t[4]}\tstated-not-accepted {t[5]}\taccepted-not-stated {t[6]}")
    if log:
        nc = not_classed(accepted, classed_names(log))
        with open(os.path.join(outdir, "accepted-not-classed.tsv"), "w") as o:
            o.write("module\tshape\tname\n")
            for r in nc:
                o.write("\t".join(r) + "\n")
        by = collections.Counter(s for _, s, _ in nc)
        print(f"CENSUS\taccepted user theorems with no CLASS row:  {len(nc)}  {dict(by)}")
        return 1 if any(s in ("other", "eq_ (a person's name)") for _, s, _ in nc) else 0
    return 0


def selftest():
    """the comparison on a planted case:  a stated declaration the kernel lacks, a generated lemma, and a person's
    theorem named `eq_of_x` that the referee did not class;  the census must name each, and only the last as blind."""
    src = "namespace N\ntheorem a : True := trivial\ndef f (n : Nat) : Nat := n\ntheorem eq_of_x : True := trivial\n" \
          "theorem gone : True := trivial\nend N\n"
    stated = {"M": stated_names(src)}
    accepted = {"M": [("theorem", "user", "N.a"), ("def", "user", "N.f"), ("theorem", "user", "N.f.eq_1"),
                      ("theorem", "user", "N.eq_of_x"), ("theorem", "gen", "N.f._proof_1")]}
    rows, gaps = compare(stated, accepted)
    kinds = collections.Counter((g[1], g[3]) for g in gaps)
    ok = kinds == collections.Counter({("stated-not-accepted", "N.gone"): 1, ("accepted-not-stated", "N.f.eq_1"): 1})
    nc = not_classed(accepted, {"N.a"})
    ok2 = sorted((s, n) for _, s, n in nc) == [("eq_ (a person's name)", "N.eq_of_x"), ("eq_<n>", "N.f.eq_1")]
    print(f"CENSUS_SELFTEST\tstated-vs-accepted {'ok' if ok else 'FAIL'}\tnot-classed {'ok' if ok2 else 'FAIL'}")
    return 0 if ok and ok2 else 1


def main(argv):
    if "--selftest" in argv:
        return selftest()
    opts = dict(a[2:].split("=", 1) for a in argv if a.startswith("--") and "=" in a)
    if not {"project", "modules", "out"} <= set(opts):
        print(__doc__)
        return 1
    return run(opts["project"], opts["modules"].split(","), opts["out"], opts.get("referee-log"))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
