"""log.py -- the project log: the human's words, verbatim, connected to the record.

WHY.  The human's side of the work is the part most easily lost.  A decision adopted in a
document the model never saw; a question asked three times in other words that the record
says nobody asked; a connection the human made by hand because the model's memory of the
record failed.  Every one of those is a human's contribution that was never in a file, so it
could not be retrieved, so it was re-derived or lost.  This module gives the human a flag
and a template, and turns each flagged block into an append-only entry that names what it
connects to -- resolved against the results index and the name registry, never against
memory.

THE FLAG.  A line that begins  [[LOG]]  opens a block; a line  [[/LOG]]  closes it
(optional -- the block runs to the end of the message).  A disposition may follow the
flag:  [[LOG hold]]  (default),  [[LOG connect]],  [[LOG draft: <target>]].

THE TEMPLATE (inside the block; only 'what' and 'connects' are required):
    what:      <the text to be logged, verbatim>
    connects:  <item>; <item>; ...     (an item name, a registered word, a file, #N)
    how:       <item> -- <relation>     (depends on / extends / contradicts /
               same as / instance of / renames / question about / answers)
    because:   <plain English, optional>
    do:        hold | connect | draft: <target>   (overrides the flag's)

USAGE.
    python3 -m discipline.log add   MESSAGE.txt  [--index RESULTS-INDEX.md] [--names NAMES.md] [--log PROJECT-LOG.md]
    python3 -m discipline.log add   -            (read the message from stdin)
    python3 -m discipline.log pending [--log PROJECT-LOG.md]            held entries, grouped by target
    python3 -m discipline.log triggers [--threshold 3]                   targets with >= N held entries
    python3 -m discipline.log resolve L-0007 --status "connected -> <where>"

Every entry is appended, never edited; status changes are appended as lines.  Resolution
prints rows: each 'connects' item with the file:line it resolved to, or UNRESOLVED.  An
unresolved item is a finding (a name missing from the registry or a result missing from
the index), not an error.  The label written above each verbatim entry is DISCIPLINE_AUTHOR
(default "Author").
"""
import re, sys, datetime
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import config

OPEN = re.compile(r"^\s*\[\[LOG(?:\s+(hold|connect|draft(?::\s*[^\]]+)?))?\s*\]\]\s*$", re.I)
CLOSE = re.compile(r"^\s*\[\[/LOG\]\]\s*$", re.I)
FIELD = re.compile(r"^\s*(what|connects|how|because|do)\s*:\s*(.*)$", re.I)
IDPAT = re.compile(r"^## (L-\d{4})\b", re.M)


def extract(text):
    """yield (disposition, fields) for every flagged block in a message."""
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = OPEN.match(lines[i])
        if not m:
            i += 1; continue
        disp = (m.group(1) or "hold").strip()
        fields, cur = {}, None
        i += 1
        while i < len(lines) and not CLOSE.match(lines[i]) and not OPEN.match(lines[i]):
            f = FIELD.match(lines[i])
            if f:
                cur = f.group(1).lower(); fields[cur] = f.group(2).strip()
            elif cur and lines[i].strip():
                fields[cur] += "\n" + lines[i].rstrip()
            i += 1
        if i < len(lines) and CLOSE.match(lines[i]):
            i += 1
        if fields.get("do"):
            disp = fields["do"].strip()
        yield disp, fields


def load_index(path):
    rows = []
    if path and Path(path).exists():
        for line in Path(path).read_text(errors="replace").splitlines():
            if line.startswith("#") or " | " not in line:
                continue
            parts = [p.strip() for p in line.split(" | ")]
            if len(parts) >= 2:
                claim = " | ".join(p for p in parts[2:] if p).strip(" |")
                rows.append((parts[0], parts[1], claim))
    return rows


def load_names(path):
    names = {}
    if path and Path(path).exists():
        for line in Path(path).read_text(errors="replace").splitlines():
            if not line.strip() or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("|")]
            names[parts[0].lower()] = parts[1] if len(parts) > 1 else ""
    return names


def norm(s):
    return (s.lower().replace("∅", "empty").replace("= empty", "= empty")
            .replace("  ", " ").strip())


def resolve(item, index, names):
    """rows for one 'connects' item: (kind, where, claim)."""
    key = item.strip()
    hits = []
    low = norm(key)
    names = {norm(k): v for k, v in names.items()}
    if low in names:
        hits.append(("name", "NAMES.md", names[low] or "(registered, no definition)"))
    # exact item match (an item name, #N) then substring on file names
    for where, it, claim in index:
        if it.lower() == low or it.lower() == low.lstrip("#"):
            hits.append(("index", where, claim))
    if not hits:
        for where, it, claim in index:
            if low in where.lower() or (len(low) > 3 and low in claim.lower()):
                hits.append(("index", where, claim))
                if len(hits) >= 5:
                    break
    return hits


def next_id(log_path):
    p = Path(log_path)
    if not p.exists():
        return "L-0001"
    ids = IDPAT.findall(p.read_text(errors="replace"))
    n = max((int(i[2:]) for i in ids), default=0) + 1
    return f"L-{n:04d}"


def add(text, index_path, names_path, log_path):
    index, names = load_index(index_path), load_names(names_path)
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
    p = Path(log_path)
    if not p.exists():
        p.write_text("# PROJECT-LOG -- the human's words, verbatim, connected to the record.\n"
                     "# Append-only.  Written by discipline/log.py from [[LOG]] blocks.\n\n")
    added = []
    for disp, f in extract(text):
        if "what" not in f:
            print("  REFUSED: a [[LOG]] block with no 'what:' line"); continue
        lid = next_id(log_path)
        items = [s.strip() for s in re.split(r"[;\n]", f.get("connects", "")) if s.strip()]
        hows = {}
        for h in re.split(r"\n", f.get("how", "")):
            if "--" in h:
                a, b = h.split("--", 1); hows[a.strip().lower()] = b.strip()
        entry = [f"## {lid} · {stamp} · {disp}", "", f"{config.author()} (verbatim):"]
        entry += ["> " + l for l in f["what"].splitlines()]
        entry += ["", "connects:"]
        unresolved = 0
        for it in items:
            hits = resolve(it, index, names)
            rel = hows.get(it.lower(), "")
            if not hits:
                unresolved += 1
                entry.append(f"- {it} — UNRESOLVED (not in the index or the registry)" + (f" — {rel}" if rel else ""))
            else:
                k, where, claim = hits[0]
                entry.append(f"- {it} ({where}) — {claim[:100]}" + (f" — {rel}" if rel else ""))
                for k2, w2, c2 in hits[1:3]:
                    entry.append(f"    also {w2} — {c2[:80]}")
        if f.get("because"):
            entry += ["", "because: " + f["because"].replace("\n", " ")]
        entry += ["", "restated (model, registered names): [to be filled by the model in the reply]",
                  f"status: {'held' if disp.startswith('hold') else disp}", ""]
        with p.open("a") as fh:
            fh.write("\n".join(entry) + "\n")
        added.append((lid, disp, len(items), unresolved))
        print(f"  {lid}  {disp:<10} {len(items)} connection(s), {unresolved} unresolved")
        for line in entry[4 + len(f['what'].splitlines()):]:
            if line.startswith("- ") or line.startswith("    also"):
                print("   " + line)
    return added


def entries(log_path):
    """one row per id: (id, latest status, connects) -- status lines appended later win."""
    p = Path(log_path)
    if not p.exists():
        return []
    text = p.read_text(errors="replace")
    blocks = re.split(r"(?m)^## (?=L-\d{4})", text)[1:]
    by = {}
    for b in blocks:
        head, _, body = b.partition("\n")
        lid = head.split(" · ")[0].strip()
        status = [l for l in body.splitlines() if l.startswith("status:")]
        conns = [l[2:].split(" — ")[0].split(" (")[0].strip() for l in body.splitlines() if l.startswith("- ")]
        cur = by.setdefault(lid, [lid, "?", []])
        if status:
            cur[1] = status[-1][7:].strip()
        if conns:
            cur[2] = conns
    return [tuple(v) for v in by.values()]


def pending(log_path, quiet=False):
    by = {}
    for lid, status, conns in entries(log_path):
        if status.startswith("held"):
            for c in conns:
                by.setdefault(c, []).append(lid)
    if not quiet:
        for c, ids in sorted(by.items(), key=lambda kv: -len(kv[1])):
            print(f"  {c:<24} {len(ids):>3} held   {', '.join(ids)}")
        if not by:
            print("  no held entries")
    return by


def triggers(log_path, threshold):
    by = pending(log_path, quiet=True)
    hot = {c: ids for c, ids in by.items() if len(ids) >= threshold}
    if not hot:
        print(f"  no target has {threshold} or more held entries")
    for c, ids in hot.items():
        print(f"  DRAFT TRIGGER  {c}: {len(ids)} held entries ({', '.join(ids)}) -- propose an iterative draft")
    return hot


def set_status(log_path, lid, status):
    p = Path(log_path)
    with p.open("a") as fh:
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%MZ")
        fh.write(f"## {lid} · {stamp} · status\nstatus: {status}\n\n")
    print(f"  {lid} status: {status}")


def main(argv):
    if not argv:
        print(__doc__); return 2
    cmd, rest = argv[0], argv[1:]
    def opt(name, default):
        if name in rest:
            i = rest.index(name); v = rest[i + 1]; del rest[i:i + 2]; return v
        return default
    reg_dir = config.registers()
    log_path = opt("--log", str(reg_dir / "PROJECT-LOG.md"))
    if cmd == "add":
        index_path = opt("--index", str(config.space() / "RESULTS-INDEX.md"))
        names_path = opt("--names", str(reg_dir / "NAMES.md"))
        src = rest[0] if rest else "-"
        text = sys.stdin.read() if src == "-" else Path(src).read_text(errors="replace")
        return 0 if add(text, index_path, names_path, log_path) else 1
    if cmd == "pending":
        pending(log_path); return 0
    if cmd == "triggers":
        th = int(opt("--threshold", "3")); triggers(log_path, th); return 0
    if cmd == "resolve":
        set_status(log_path, rest[0], opt("--status", "connected")); return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
