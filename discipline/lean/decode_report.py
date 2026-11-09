"""decode_report.py -- the decode step's report and controls (DECODE-DESIGN.md).

usage:  python3 decode_report.py LIBRARY.tsv DDECL.tsv[,DDECL2.tsv...] CONTROLS.tsv OUTDIR [--shuffles=1000]

LIBRARY.tsv is the output of `referee_lean.py --decode-library`, DDECL.tsv of `--decode-out` (the project's definitions,
unpacked).  Writes OUTDIR/decode.tsv (every definition and its ranked candidates) and OUTDIR/decode-controls.json
(controls 1-4).  A candidate is a lead, not a status:  only a proved bridge gives one.

Needs numpy and scipy (the shuffle scores every definition 1,000 times)."""
import csv, json, os, random, sys
import numpy as np
from scipy import sparse

csv.field_size_limit(10**8)
J_MIN, SHARED_MIN, TOP = 0.5, 2, 10
TWIN_KINDS = {"def", "structure", "class", "inductive"}
SIDE_HEADS = {"Iff", "Eq", "Equiv"}


def sets(field):
    return [] if field in ("-", "") else field.split(",")


def load_library(path):
    rows = []
    for ln in open(path, encoding="utf-8"):
        p = ln.rstrip("\n").split("\t")
        if p[0] != "MDECL" or len(p) < 10:
            continue
        _, name, kind, origin, head, lh, rh, lhs, rhs, cs = p[:10]
        rows.append((name, kind, origin, head, lh, rh, sets(lhs), sets(rhs), sets(cs)))
    return rows


def load_ddecl(paths):
    out = {}
    for path in paths:
        for ln in open(path, encoding="utf-8"):
            p = ln.rstrip("\n").split("\t")
            if p[0] == "DDECL" and len(p) >= 7:
                out[p[1]] = (p[3], sets(p[4]), sets(p[5]), p[6])
    return out


class Index:
    """three sparse matrices over one vocabulary:  twins (whole sets of definitions and types), and the two sides of
    every `↔`, `=` and `≃` conclusion."""

    def __init__(self, lib):
        self.vocab = {}
        self.twin_rows, self.side_rows = [], []      # (row in lib, set) ; (row in lib, set, other side's head)
        for i, (name, kind, origin, head, lh, rh, ls, rs, cs) in enumerate(lib):
            if kind in TWIN_KINDS and cs:
                self.twin_rows.append((i, cs, name))
            if head in SIDE_HEADS:
                if ls and rh not in ("-", ""):
                    self.side_rows.append((i, ls, rh))
                if rs and lh not in ("-", ""):
                    self.side_rows.append((i, rs, lh))
        for _, s, _ in self.twin_rows + self.side_rows:
            for c in s:
                self.vocab.setdefault(c, len(self.vocab))
        self.T, self.tsz = self._mat(self.twin_rows)
        self.S, self.ssz = self._mat(self.side_rows)
        self.lib = lib

    def _mat(self, rows):
        r, c = [], []
        for k, (_, s, _) in enumerate(rows):
            for x in set(s):
                r.append(k)
                c.append(self.vocab[x])
        m = sparse.csr_matrix((np.ones(len(r), dtype=np.float32), (r, c)), shape=(len(rows), len(self.vocab) or 1))
        return m, np.asarray(m.sum(axis=1)).ravel()

    def vec_cols(self, usets):
        """a vocabulary x definitions matrix (constants outside the vocabulary count only in the set's size)."""
        r, c = [], []
        for j, u in enumerate(usets):
            for x in set(u):
                if x in self.vocab:
                    r.append(self.vocab[x])
                    c.append(j)
        return sparse.csr_matrix((np.ones(len(r), dtype=np.float32), (r, c)), shape=(len(self.vocab) or 1, len(usets)))

    def hits(self, usets):
        """for each set:  (rows of T, rows of S) passing J >= 1/2 with at least two shared constants."""
        U = self.vec_cols(usets)
        usz = np.array([len(set(u)) for u in usets], dtype=np.float32)
        out = []
        ST, SS = (self.T @ U).tocsc(), (self.S @ U).tocsc()
        for j in range(len(usets)):
            res = []
            for M, sz in ((ST, self.tsz), (SS, self.ssz)):
                col = M.getcol(j)
                idx, sh = col.indices, col.data
                jac = sh / (sz[idx] + usz[j] - sh)
                keep = (sh >= SHARED_MIN) & (jac >= J_MIN)
                res.append(list(zip(idx[keep].tolist(), jac[keep].tolist())))
            out.append(res)
        return out


def candidates(ix, hit):
    """ranked candidates:  J, then twins before characterisations, then name length;  one entry per name."""
    best = {}
    twins, chars = hit
    for k, j in twins:
        i, _, name = ix.twin_rows[k]
        key = (-j, 0, len(name))
        if name not in best or key < best[name][0]:
            best[name] = (key, "twin", name)
    for k, j in chars:
        i, _, other = ix.side_rows[k]
        ev = ix.lib[i][0]
        key = (-j, 1, len(other))
        if other not in best or key < best[other][0]:
            best[other] = (key, "char", ev)
    ranked = sorted(best.items(), key=lambda kv: kv[1][0])
    return [(name, round(-v[0][0], 3), v[1], v[2]) for name, v in ranked]


def main(argv):
    lib_path, dd_paths, ctl_path, outdir = argv[0], argv[1].split(","), argv[2], argv[3]
    shuffles = 1000
    for a in argv[4:]:
        if a.startswith("--shuffles="):
            shuffles = int(a.split("=", 1)[1])
    os.makedirs(outdir, exist_ok=True)
    lib = load_library(lib_path)
    dd = load_ddecl(dd_paths)
    ix = Index(lib)
    names = sorted(dd)
    usets = [dd[n][1] for n in names]
    hits = ix.hits(usets)
    cands = {n: candidates(ix, h) for n, h in zip(names, hits)}
    with open(os.path.join(outdir, "decode.tsv"), "w") as f:
        w = csv.writer(f, delimiter="\t", lineterminator="\n")
        w.writerow(["definition", "module", "unpacked", "stops", "rounds", "candidates", "top"])
        for n in names:
            mod, u, st, rd = dd[n]
            top = " ; ".join(f"{c} ({j}, {r}{'' if r == 'twin' else ': ' + e})" for c, j, r, e in cands[n][:TOP])
            w.writerow([n, mod, ",".join(u) or "-", ",".join(st) or "-", rd, len(cands[n]), top or "-"])
    # controls 1 and 2
    res = {"library_rows": len(lib), "definitions": len(names), "known": {}, "heldout": {}}
    for ln in open(ctl_path, encoding="utf-8"):
        if ln.startswith("#") or not ln.strip():
            continue
        st, row, proj, exp = ln.rstrip("\n").split("\t")
        exps = exp.split(",")
        top = [c for c, _, _, _ in cands.get(proj, [])[:TOP]]
        rank = next((k + 1 for k, c in enumerate(top) if c in exps), None)
        res[st][row] = {"definition": proj, "decoded": proj in dd, "expected": exps, "rank": rank,
                        "top": top[:5], "stops": dd[proj][2] if proj in dd else None}
    for st, need in (("known", 14), ("heldout", 8)):
        found = sum(1 for v in res[st].values() if v["rank"])
        res[st + "_found"] = found
        res[st + "_total"] = len(res[st])
        res[st + "_pass"] = found >= need
    # control 3:  the planted absence (namespace RefereeDecodeControls, the definitions on the planted inductive)
    planted = [n for n in names if n.startswith("RefereeDecodeControls.tritonic")]
    res["absence"] = {n: len(cands[n]) for n in planted}
    res["absence_pass"] = bool(planted) and all(v == 0 for v in res["absence"].values())
    fire = "RefereeDecodeControls.addOut"
    res["planted_fire"] = {"definition": fire, "top": [c for c, _, _, _ in cands.get(fire, [])[:TOP]]}
    res["planted_fire_pass"] = "Nat.add" in res["planted_fire"]["top"]
    # control 4:  the shuffle (the pooled constants dealt back at random, sizes kept, no repeats in a set)
    scope = [k for k, n in enumerate(names) if not n.startswith("RefereeDecodeControls.")]
    real = sum(1 for k in scope if cands[names[k]]) / max(1, len(scope))
    pool = [c for k in scope for c in usets[k]]
    sizes = [len(usets[k]) for k in scope]
    rnd = random.Random(20261030)
    null = []
    for _ in range(shuffles):
        rnd.shuffle(pool)
        dealt, p = [], 0
        rest = list(pool)
        for s in sizes:
            chosen, keep = [], []
            seen = set()
            for c in rest:
                if len(chosen) < s and c not in seen:
                    chosen.append(c)
                    seen.add(c)
                else:
                    keep.append(c)
            rest = keep
            dealt.append(chosen)
        h = ix.hits(dealt)
        null.append(sum(1 for x in h if x[0] or x[1]) / max(1, len(scope)))
    null.sort()
    p95 = null[int(0.95 * len(null)) - 1] if null else None
    res["shuffle"] = {"real_rate": real, "null_mean": sum(null) / len(null) if null else None, "null_p95": p95,
                      "null_max": null[-1] if null else None, "shuffles": shuffles}
    res["shuffle_pass"] = p95 is not None and real > p95
    json.dump(res, open(os.path.join(outdir, "decode-controls.json"), "w"), indent=1, ensure_ascii=False)
    for k in ("known_found", "known_total", "known_pass", "heldout_found", "heldout_total", "heldout_pass",
              "absence_pass", "planted_fire_pass", "shuffle_pass"):
        print(k, res[k])
    print("shuffle", res["shuffle"])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
