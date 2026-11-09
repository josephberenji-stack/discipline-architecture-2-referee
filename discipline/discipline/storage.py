"""storage.py -- where final files live, and a quick check between full reindexes.

WHY.  A full reindex walks every file the index reads and confirms every citation
resolves; it is the authoritative check and it is slow.  Between two full reindexes there
is no cheap way to know whether anything the index reads has changed, and no way at all to
know whether a mirror of the final files is still an exact copy of the canonical ones.
This module records what the last full reindex saw, compares the present against it, and
keeps one mirror exact -- so that a full scan is run when it is due and not every time.

THE RULE.  One space is canonical and cited; every other copy is a mirror and is never
cited or indexed.  reindex.sh indexes the canonical space only; the mirror is kept exact
by `mirror`, and `quick` proves it.

CONFIGURATION.  registers/storage.cfg, key = value, one per line:
    part      NAME=PATH        a root the index reads, named (repeatable; the first is the
                               space itself when omitted)
    canonical GLOB             a glob, relative to the space, naming final files that are
                               mirrored, with their .out beside them if present (repeatable)
    mirror    PATH             the mirror directory, relative to the space
    exclude   PREFIX           a path prefix, relative to a part, the index does not read
                               (repeatable)

COMMANDS.  python3 -m discipline.storage mirror     copy every canonical file whose mirror
                                                    is missing or differs; never deletes;
                                                    writes registers/MIRROR-MANIFEST.tsv
           python3 -m discipline.storage snapshot   (run by reindex.sh after a full reindex)
                                                    record every indexed file (size, mtime,
                                                    md5) per part in
                                                    registers/INDEX-MANIFEST.tsv
           python3 -m discipline.storage quick      compare the present against the last
                                                    snapshot and the mirror against the
                                                    canonical space; exit 0 when both are
                                                    current, 2 when a full reindex is due,
                                                    3 when the mirror has drifted
Stat (size, mtime) is compared first; an md5 is read only where the stat differs, so
`quick` is fast.  Standard library only.
"""
import hashlib, os, re, sys, time
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

SPACE = config.space()
REG = config.registers(SPACE)
IMAN = REG / "INDEX-MANIFEST.tsv"
MMAN = REG / "MIRROR-MANIFEST.tsv"


def load_cfg():
    cfg = {"part": [], "canonical": [], "mirror": None, "exclude": []}
    p = REG / "storage.cfg"
    if not p.is_file():
        return cfg
    for line in p.read_text(errors="replace").splitlines():
        line = line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        k, _, v = line.partition("=")
        k, v = k.strip(), v.strip()
        if k == "mirror":
            cfg["mirror"] = v
        elif k in cfg:
            cfg[k].append(v)
    return cfg


CFG = load_cfg()


def md5(p):
    h = hashlib.md5()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def roots():
    """The parts the index reads: (name, path).  The space itself unless parts are configured."""
    parts = []
    for spec in CFG["part"]:
        name, _, path = spec.partition("=")
        path = Path(path.strip()).expanduser()
        if not path.is_absolute():
            path = SPACE / path
        if path.is_dir():
            parts.append((name.strip(), path.resolve()))
    if not parts:
        parts = [(SPACE.name, SPACE)]
    return parts


def mirror_dir():
    if not CFG["mirror"]:
        return None
    m = Path(CFG["mirror"]).expanduser()
    return m if m.is_absolute() else SPACE / m


def indexed_files(tag, root):
    for f in sorted(root.rglob("*")):
        if f.suffix not in config.INDEXED or config.skipped(f) or not f.is_file():
            continue
        rel = f.relative_to(root).as_posix()
        if any(rel == e or rel.startswith(e) for e in CFG["exclude"]):
            continue
        yield rel, f


def cite(p):
    """A path as a citation writes it: relative to the part that holds it."""
    p = p.resolve()
    for tag, root in roots():
        if root in p.parents:
            return tag + "/" + p.relative_to(root).as_posix()
    return str(p)


def canonical_pairs():
    """(canonical source, mirror destination) for every final file."""
    m = mirror_dir()
    pairs = []
    if m is None:
        return pairs
    for g in CFG["canonical"]:
        for f in sorted(SPACE.glob(g)):
            if not f.is_file():
                continue
            sub = f.suffix.lstrip(".") or "other"
            pairs.append((f, m / sub / f.name))
            o = f.with_suffix(".out")
            if o.is_file() and o != f:
                pairs.append((o, m / sub / o.name))
    return pairs


def cmd_mirror():
    import shutil
    m = mirror_dir()
    if m is None:
        print("mirror: no mirror configured (registers/storage.cfg: mirror = PATH)"); return 0
    rows, copied, same = [], 0, 0
    for src, dst in canonical_pairs():
        dst.parent.mkdir(parents=True, exist_ok=True)
        h = md5(src)
        if not dst.is_file() or md5(dst) != h:
            shutil.copy2(src, dst); copied += 1
        else:
            same += 1
        rows.append(f"{cite(src)}\t{dst.relative_to(SPACE) if SPACE in dst.parents else dst}\t{h}\t{src.stat().st_size}")
    known = {d for _, d in canonical_pairs()}
    orphans = [p for p in m.rglob("*") if p.is_file() and p.name != ".DS_Store" and p not in known]
    REG.mkdir(parents=True, exist_ok=True)
    MMAN.write_text(f"# MIRROR-MANIFEST -- written by storage.py mirror, {time.strftime('%Y-%m-%d %H:%M:%S')}\n"
                    "# canonical\tmirror\tmd5\tbytes\n" + "\n".join(rows) + "\n")
    print(f"mirror: {len(rows)} files; copied {copied}; already exact {same}; orphans in the mirror {len(orphans)}")
    for p in orphans[:20]:
        print(f"   orphan (no canonical source): {p}")
    return 0


def cmd_snapshot():
    out = [f"# INDEX-MANIFEST -- written by storage.py snapshot after a full reindex, {time.strftime('%Y-%m-%d %H:%M:%S')}",
           "# part\tpath\tbytes\tmtime_ns\tmd5"]
    n = {}
    for tag, root in roots():
        for rel, f in indexed_files(tag, root):
            st = f.stat()
            out.append(f"{tag}\t{rel}\t{st.st_size}\t{st.st_mtime_ns}\t{md5(f)}")
            n[tag] = n.get(tag, 0) + 1
    ri = SPACE / "RESULTS-INDEX.md"
    rows = sum(1 for l in open(ri, errors="replace") if l.strip() and not l.startswith("#")) if ri.is_file() else 0
    out.insert(2, f"# parts: {', '.join(f'{t} {c} files' for t, c in n.items())}; RESULTS-INDEX.md rows {rows}")
    REG.mkdir(parents=True, exist_ok=True)
    IMAN.write_text("\n".join(out) + "\n")
    print(f"snapshot: {sum(n.values())} indexed files recorded ({', '.join(f'{t} {c}' for t, c in n.items())})")
    return 0


def cmd_quick():
    t0 = time.time()
    if not IMAN.is_file():
        print("quick: no INDEX-MANIFEST.tsv -- run sh reindex.sh once (full)"); return 2
    old = {}
    head = []
    for l in open(IMAN, errors="replace"):
        if l.startswith("#"):
            head.append(l.rstrip()); continue
        tag, rel, size, mt, h = l.rstrip("\n").split("\t")
        old[(tag, rel)] = (int(size), int(mt), h)
    added, changed, touched = [], [], 0
    seen = set()
    for tag, root in roots():
        for rel, f in indexed_files(tag, root):
            k = (tag, rel); seen.add(k)
            st = f.stat()
            if k not in old:
                added.append(k); continue
            size, mt, h = old[k]
            if st.st_size == size and st.st_mtime_ns == mt:
                continue
            touched += 1
            if md5(f) != h:
                changed.append(k)
    removed = [k for k in old if k not in seen]
    drift, missing = [], []
    for src, dst in canonical_pairs():
        if not dst.is_file():
            missing.append(dst); continue
        a, b = src.stat(), dst.stat()
        if a.st_size != b.st_size or md5(src) != md5(dst):
            drift.append(dst)
    print(head[0] if head else "")
    print(head[2] if len(head) > 2 else "")
    print(f"quick: since the last full reindex -- added {len(added)}, changed {len(changed)}, removed {len(removed)}"
          f" (stat differed on {touched}, content on {len(changed)})")
    for label, ks in (("added", added), ("changed", changed), ("removed", removed)):
        for tag, rel in ks[:25]:
            print(f"   {label:8s} {tag}/{rel}")
        if len(ks) > 25:
            print(f"   ... and {len(ks) - 25} more {label}")
    if mirror_dir() is not None:
        print(f"quick: mirror -- {len(canonical_pairs())} canonical files; missing in the mirror {len(missing)};"
              f" differing {len(drift)}")
        for p in (missing + drift)[:25]:
            print(f"   mirror    {p}")
    print(f"quick: {time.time() - t0:.1f}s")
    if missing or drift:
        print("quick: MIRROR NOT EXACT -- run python3 -m discipline.storage mirror"); return 3
    if added or changed or removed:
        print("quick: FULL REINDEX DUE -- run sh reindex.sh"); return 2
    print("quick: index current; mirror exact."); return 0


if __name__ == "__main__":
    c = sys.argv[1] if len(sys.argv) > 1 else "quick"
    sys.exit({"mirror": cmd_mirror, "snapshot": cmd_snapshot, "quick": cmd_quick}.get(c, lambda: sys.exit(
        "usage: storage.py mirror | snapshot | quick"))())
