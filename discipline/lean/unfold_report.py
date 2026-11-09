"""unfold_report.py -- the reports of the unfold pass, over a whole package.

    python3 unfold_report.py --in=DIR [--library=FILE] --out=DIR [--compare=OLD_OUT_DIR]

DIR holds the `*.unfold.tsv` files that `referee_lean.py --unfold-out=DIR` wrote (one per referee run);  FILE is the
outside library's structures (`referee_lean.py --unfold-library=FILE`).  Written to the output folder:

    summary.md        the counts:  declarations by kind, theorems by what carries them (R1k), the package checks
    inventory.tsv     module, kind, count
    decls.tsv         every declaration:  name, kind, module, flags, type
    r1k.tsv           every theorem:  name, module, r1k, rfl, decide, first content, stored axioms read, hypotheses
                      that are project propositions, recursors
    carriers.tsv      every carrier:  a project proposition used as a hypothesis, or a stored axiom (a proposition field)
                      read by a proof;  the theorems that use it directly and every theorem downstream of those (through
                      the proof graph), and whether it is established on file
    counterparts.tsv  every project structure and class:  its fields, the outside-library classes it already has
                      instances of, and the outside-library structures with the most similar field names (candidates for a
                      person or a proved equivalence to decide;  a field name is not a morphism)
    checks.tsv        the package checks UNFOLD, BRIDGED, CARRIER (`referee_lean.package_checks`) over the whole package
    r1k-changes.tsv   (with --compare) every theorem whose R1k changed since the earlier report, and the ones added or gone

Nothing here is a verdict on a theorem's mathematics:  the reports say what each declaration is built from.
"""
import collections, glob, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import referee_lean  # noqa: E402  (package_checks)


def read_lines(paths):
    out = []
    for p in paths:
        for ln in open(p, encoding="utf-8", errors="replace"):
            ln = ln.rstrip("\n")
            if ln:
                out.append(ln.split("\t"))
    return out


def jaccard(a, b):
    return len(a & b) / len(a | b) if a | b else 0.0


def main(argv):
    args = dict(a[2:].split("=", 1) for a in argv if a.startswith("--") and "=" in a)
    src, out = args["in"], args["out"]
    os.makedirs(out, exist_ok=True)
    ul = read_lines(sorted(glob.glob(os.path.join(src, "*.unfold.tsv"))))
    lib = read_lines([args["library"]]) if "library" in args else []

    decl = {f[1]: f for f in ul if f[0] == "DECL" and len(f) >= 6}
    thm = {f[1]: f for f in ul if f[0] == "THM" and len(f) >= 13}
    fields = collections.defaultdict(list)
    for f in ul:
        if f[0] == "FIELD" and len(f) >= 5:
            fields[f[1]].append((f[2], f[3] == "true", f[4]))
    instof = collections.defaultdict(set)
    for f in ul:
        if f[0] == "INSTOF" and len(f) >= 5:
            for ty in f[4].split(","):
                if ty and ty != "-":
                    instof[ty].add((f[2], f[3]))
    # the proof graph among project declarations:  who uses whom
    users = collections.defaultdict(set)
    for f in ul:
        if f[0] == "EDGE" and len(f) >= 6 and f[5] == "project":
            users[f[2]].add(f[1])

    # inventory, decls
    inv = collections.Counter((f[3], f[2]) for f in decl.values())
    with open(os.path.join(out, "inventory.tsv"), "w") as w:
        w.write("module\tkind\tcount\n")
        for (m, k), n in sorted(inv.items()):
            w.write(f"{m}\t{k}\t{n}\n")
    with open(os.path.join(out, "decls.tsv"), "w") as w:
        w.write("name\tkind\tmodule\tflags\ttype\n")
        for n in sorted(decl):
            f = decl[n]
            w.write("\t".join([n, f[2], f[3], f[4], f[5]]) + "\n")
    # r1k
    with open(os.path.join(out, "r1k.tsv"), "w") as w:
        w.write("theorem\tmodule\tr1k\trfl\tdecide\tfirst_content\tstored_axioms\thypotheses\trecursors\n")
        for n in sorted(thm):
            f = thm[n]
            mod = decl.get(n, [None] * 4)[3] or "-"
            w.write("\t".join([n, mod, f[2], f[8], f[7], f[3], f[4], f[5], f[6]]) + "\n")

    # carriers:  direct users, downstream theorems, established
    direct = collections.defaultdict(set)
    kind = {}
    for n, f in thm.items():
        for h in f[5].split(","):
            if h and h != "-":
                direct[h].add(n)
                kind[h] = "hypothesis"
        for a in f[4].split(","):
            if a and a != "-":
                direct[a].add(n)
                kind[a] = "stored axiom"
    established = {f[11] for f in thm.values() if f[11] != "-" and f[11] not in f[5].split(",")}

    def downstream(start):
        seen, todo = set(start), list(start)
        while todo:
            x = todo.pop()
            for u in users.get(x, ()):
                if u not in seen and u in thm:
                    seen.add(u)
                    todo.append(u)
        return seen - set(start)

    carriers = []
    for c, ds in direct.items():
        down = downstream(ds)
        est = "-" if kind[c] == "stored axiom" else ("yes" if c in established else "no")
        carriers.append((len(ds) + len(down), c, kind[c], len(ds), len(down), est))
    carriers.sort(reverse=True)
    with open(os.path.join(out, "carriers.tsv"), "w") as w:
        w.write("carrier\tkind\tdirect_theorems\tdownstream_theorems\testablished\n")
        for tot, c, k, d, dn, est in carriers:
            w.write(f"{c}\t{k}\t{d}\t{dn}\t{est}\n")

    # counterparts
    libs = {}
    for f in lib:
        if f[0] == "MSTRUCT" and len(f) >= 5:
            fs = {x.split(".")[-1] for x in f[4].split(",") if x}
            if len(fs) >= 2:
                libs[f[1]] = (fs, f[3])
    with open(os.path.join(out, "counterparts.tsv"), "w") as w:
        w.write("structure\tkind\tmodule\tfields\tprop_fields\toutside_instances\tcandidates (name: shared fields / jaccard)\n")
        for s in sorted(n for n, f in decl.items() if f[2] in ("structure", "class")):
            fs = fields.get(s, [])
            names = {x[0] for x in fs}
            cands = []
            if len(names) >= 2:
                for ln, (lf, _) in libs.items():
                    j = jaccard(names, lf)
                    if j >= 0.5 and len(names & lf) >= 2:
                        cands.append((j, ln, len(names & lf)))
                cands.sort(reverse=True)
            ins = sorted(c for c, o in instof.get(s, ()) if o == "mathlib")
            w.write("\t".join([s, decl[s][2], decl[s][3], ",".join(x[0] for x in fs) or "-",
                               str(sum(1 for x in fs if x[1])), ",".join(ins) or "-",
                               "; ".join(f"{ln}: {k} / {j:.2f}" for j, ln, k in cands[:3]) or "-"]) + "\n")

    # the package checks
    rows = referee_lean.package_checks(ul, [])
    with open(os.path.join(out, "checks.tsv"), "w") as w:
        for r in rows:
            w.write("REFEREE\t" + "\t".join(r) + "\n")

    # compare with an earlier report
    changes = []
    if "compare" in args:
        old = {}
        for ln in open(os.path.join(args["compare"], "r1k.tsv"), encoding="utf-8"):
            f = ln.rstrip("\n").split("\t")
            if f[0] != "theorem":
                old[f[0]] = f[2]
        new = {n: f[2] for n, f in thm.items()}
        for n in sorted(set(old) | set(new)):
            a, b = old.get(n, "absent"), new.get(n, "absent")
            if a != b:
                changes.append((n, a, b))
        with open(os.path.join(out, "r1k-changes.tsv"), "w") as w:
            w.write("theorem\tbefore\tafter\n")
            for c in changes:
                w.write("\t".join(c) + "\n")

    # summary
    kinds = collections.Counter(f[2] for f in decl.values())
    r1k = collections.Counter(f[2] for f in thm.values())
    chk = collections.Counter((r[0], r[2]) for r in rows)
    with open(os.path.join(out, "summary.md"), "w") as w:
        w.write(f"# Unfold report\n\n- unfold files: {len(glob.glob(os.path.join(src, '*.unfold.tsv')))}; "
                f"library structures: {len(libs)}\n- declarations: {len(decl)}\n\n## Declarations by kind\n\n")
        for k, n in kinds.most_common():
            w.write(f"- {k}: {n}\n")
        w.write("\n## Theorems by what carries them (R1k)\n\n")
        for k, n in r1k.most_common():
            w.write(f"- {k}: {n}\n")
        w.write("\n## Package checks\n\n")
        for (c, s), n in sorted(chk.items()):
            w.write(f"- {c} {s}: {n}\n")
        w.write("\n## The ten largest carriers (direct + downstream theorems)\n\n")
        for tot, c, k, d, dn, est in carriers[:10]:
            w.write(f"- {c} ({k}): {d} direct, {dn} downstream, established {est}\n")
        if "compare" in args:
            w.write(f"\n## Changes since {args['compare']}\n\n- theorems whose R1k changed, added or gone: {len(changes)}\n")
            for (a, b), n in collections.Counter((a, b) for _, a, b in changes).most_common(12):
                w.write(f"- {a} -> {b}: {n}\n")
    print(open(os.path.join(out, "summary.md")).read())
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
