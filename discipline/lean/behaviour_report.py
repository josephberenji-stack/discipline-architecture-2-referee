#!/usr/bin/env python3
"""behaviour_report.py -- the behaviour step's report and controls (BEHAVIOUR-DESIGN.md, § 5 and the controls).

    python3 behaviour_report.py --rows=ROWS.tsv --raw=rows.raw [--pairs-raw=pairs.raw] --out=DIR

Reads the BEHAVE lines that `Behaviour.lean` printed (`#referee_behave`, `#referee_behave_pair`) and writes

    DIR/behaviour.tsv    one line per reported candidate:  row, definition, shape, rank, candidate, S, ok, tested,
                         value, failed laws
    DIR/controls.json    controls 1, 2, 3, 4, 5 and 7 with their numbers and PASS / FAIL;  control 6 is the
                         self-test's (`referee_lean.py --selftest --mutations`) and is not scored here

No verdict on any definition is written:  a candidate is a lead, and only a proved bridge gives a status.
The rules (fixed by the registration):  a candidate has at least 3 laws tested, S = ok / tested >= 0.8, and value
agreement not failed where it was checked;  candidates are ranked by S, then by the number of laws tested, then by
the length of the name;  the top 10 are reported.
"""
import json
import os
import random
import sys

MIN_LAWS = 3
BAR = 0.8
TOP = 10
SEED = 20261030
PAIRINGS = 1000


def read_rows(path):
    """ROWS.tsv:  set <TAB> row <TAB> definition <TAB> expected (comma-separated), as controls/decode-controls.tsv."""
    rows = []
    for ln in open(path):
        if not ln.strip() or ln.startswith("#"):
            continue
        s, row, d, exp = ln.rstrip("\n").split("\t")[:4]
        rows.append({"set": s, "row": row, "def": d, "expected": [e for e in exp.split(",") if e]})
    return rows


def behave_lines(path):
    out = []
    for ln in open(path, errors="replace"):
        i = ln.find("BEHAVE\t")
        if i >= 0:
            out.append(ln[i:].rstrip("\n").split("\t")[1:])
    return out


def is_candidate(ok, tested, value):
    return tested >= MIN_LAWS and ok / tested >= BAR and value != "disagree"


def ranked(cands):
    """cands: list of (name, ok, tested, value, failed).  The candidates, ranked, top 10."""
    keep = [c for c in cands if is_candidate(c[1], c[2], c[3])]
    keep.sort(key=lambda c: (-c[1] / c[2], -c[2], len(c[0]), c[0]))
    return keep[:TOP]


def parse(raw):
    shapes, kinds, cands = {}, {}, {}
    for f in behave_lines(raw):
        if f[0] == "ROW":
            _, d, kind, shape, _n = f[:5]
            shapes[d], kinds[d] = shape, kind
            cands.setdefault(d, [])
        elif f[0] == "CAND":
            _, d, n, ok, tested, value, failed = f[:7]
            cands.setdefault(d, []).append((n, int(ok), int(tested), value, failed))
    return shapes, kinds, cands


def pair_scores(raw):
    out = {}
    if raw and os.path.exists(raw):
        for f in behave_lines(raw):
            if f[0] == "PAIR":
                _, d, n, ok, tested, value, failed = f[:7]
                out[(d, n)] = (int(ok), int(tested), value, failed)
    return out


def control_pairs(rows, shapes):
    """The pairs controls 4 and 7 score, fixed by the seed and the rows' shapes.  Control 4:  1,000 random pairings of
    a known or held-out D with the first expected N of a row of another shape class.  Control 7:  for every known
    row, the D of each other known row of the same shape on that row's first expected N."""
    rng = random.Random(SEED)
    scored = [r for r in rows if r["set"] in ("known", "heldout")]
    swap = []
    for _ in range(PAIRINGS):
        r = rng.choice(scored)
        others = [o for o in scored if shapes.get(o["def"], "?") != shapes.get(r["def"], "?") and o["expected"]]
        if not others:
            continue
        o = rng.choice(others)
        swap.append((r["def"], o["expected"][0]))
    known = [r for r in rows if r["set"] == "known"]
    fam = []
    for r in known:
        for o in known:
            if o is r or not r["expected"]:
                continue
            if shapes.get(o["def"]) and shapes.get(o["def"]) == shapes.get(r["def"]):
                fam.append((o["def"], r["expected"][0]))
    return swap, fam


def main(argv):
    opts = dict(a[2:].split("=", 1) for a in argv if a.startswith("--") and "=" in a)
    rows = read_rows(opts["rows"])
    shapes, kinds, cands = parse(opts["raw"])
    pairs = pair_scores(opts.get("pairs-raw"))
    out = opts["out"]
    os.makedirs(out, exist_ok=True)
    top = {}
    with open(os.path.join(out, "behaviour.tsv"), "w") as f:
        f.write("row\tdefinition\tshape\trank\tcandidate\tS\tok\ttested\tvalue\tfailed\n")
        for r in rows:
            d = r["def"]
            t = ranked(cands.get(d, []))
            top[d] = [c[0] for c in t]
            if not t:
                f.write(f"{r['row']}\t{d}\t{shapes.get(d, '-')}\t-\t-\t-\t-\t-\t-\t-\n")
            for i, (n, ok, tested, value, failed) in enumerate(t, 1):
                f.write(f"{r['row']}\t{d}\t{shapes.get(d, '-')}\t{i}\t{n}\t{ok / tested:.3f}\t{ok}\t{tested}\t"
                        f"{value}\t{failed}\n")

    def hit(r):
        return any(e in top.get(r["def"], []) for e in r["expected"])

    known = [r for r in rows if r["set"] == "known"]
    held = [r for r in rows if r["set"] == "heldout"]
    absent = [r for r in rows if r["set"] == "absent"]
    planted = [r for r in rows if r["set"] == "planted"]
    c = {}
    k = sum(hit(r) for r in known)
    c["1"] = {"control": "known answers", "found": k, "of": len(known), "needed": 14,
              "rows_found": [r["row"] for r in known if hit(r)], "result": "PASS" if k >= 14 else "FAIL"}
    h = sum(hit(r) for r in held)
    c["2"] = {"control": "held out", "found": h, "of": len(held), "needed": 8,
              "rows_found": [r["row"] for r in held if hit(r)], "result": "PASS" if h >= 8 else "FAIL"}
    a = {r["row"]: len(top.get(r["def"], [])) for r in absent}
    c["3"] = {"control": "planted absence", "candidates": a,
              "result": "PASS" if absent and all(v == 0 for v in a.values()) else "FAIL"}
    swap, fam = control_pairs(rows, shapes)
    if pairs:
        reach = [p for p in swap if p in pairs and is_candidate(*pairs[p][:3])]
        missing = [p for p in swap if p not in pairs]
        rate = len(reach) / len(swap) if swap else 0.0
        c["4"] = {"control": "cross-family swap", "pairings": len(swap), "reach": len(reach), "rate": rate,
                  "unscored": len(missing),
                  "result": "PASS" if swap and not missing and rate < 0.05 else "FAIL"}
        freach = [p for p in fam if p in pairs and is_candidate(*pairs[p][:3])]
        fmissing = [p for p in fam if p not in pairs]
        c["7"] = {"control": "other family", "pairs": len(fam), "reach": len(freach),
                  "reaching": [list(p) for p in freach], "unscored": len(fmissing),
                  "result": "PASS" if not fmissing and len(freach) <= 2 else "FAIL"}
    else:
        c["4"] = {"control": "cross-family swap", "result": "NOT RUN"}
        c["7"] = {"control": "other family", "result": "NOT RUN"}
    p5 = [r for r in planted if r["row"] == "addOut"]
    c["5"] = {"control": "planted pair", "top10": top.get(p5[0]["def"], []) if p5 else [],
              "result": "PASS" if p5 and hit(p5[0]) else "FAIL"}
    c["6"] = {"control": "mutation", "result": "the self-test's (referee_lean.py --selftest --mutations)"}
    with open(os.path.join(out, "controls.json"), "w") as f:
        json.dump(c, f, indent=1, sort_keys=True)
    for key in sorted(c):
        print(f"BEHAVIOUR\tcontrol {key}\t{c[key]['control']}\t{c[key]['result']}")
    return 0 if all(c[x]["result"] == "PASS" for x in ("1", "2", "3", "4", "5", "7")) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
