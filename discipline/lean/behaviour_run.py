#!/usr/bin/env python3
"""behaviour_run.py -- run the behaviour step (BEHAVIOUR-DESIGN.md) on a built package.

    python3 behaviour_run.py --project=PATH --rows=ROWS.tsv --imports=A.B,C.D --out=DIR [--phase=rows|pairs|all]

Phase `rows`:  one check file (the imports, Mathlib, `Behaviour.lean`'s body, the planted controls of
`controls/DecodeControls.lean`, one `#referee_behave_rows` over every row) run by `lake env lean`;  its output is DIR/rows.raw.
Phase `pairs`:  the pairs of controls 4 and 7, fixed from the rows' shapes and the seed (`behaviour_report.py`), one
`#referee_behave_pairs` over all of them;  DIR/pairs.raw.  Then `behaviour_report.py` writes DIR/behaviour.tsv and DIR/controls.json.

Lean runs with the memory cap REFEREE_MEM (MB, default 8192) and the project roots REFEREE_BEHAVE_ROOTS.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import behaviour_report as BR  # noqa: E402

MARK = "-- BODY (the marker:  everything below is pasted)\n"


def body():
    return open(os.path.join(HERE, "Behaviour.lean")).read().split(MARK, 1)[1]


def planted():
    return open(os.path.join(HERE, "controls", "DecodeControls.lean")).read()


def check_file(imports, commands):
    head = "".join(f"import {m}\n" for m in ["Mathlib"] + [m for m in imports if m and m != "Mathlib"])
    return (head + "import Lean\n" + body() + "\n" + planted() + "\nset_option maxHeartbeats 0\n"
            "set_option maxRecDepth 100000\n" + "".join(c + "\n" for c in commands))


def run(project, text, raw):
    fd, path = tempfile.mkstemp(suffix=".lean", prefix="Behave_", dir=project)
    with os.fdopen(fd, "w") as f:
        f.write(text)
    try:
        open(raw, "w").close()
        # the lines go to `raw` as they are made (REFEREE_BEHAVE_FILE);  Lean's own output to `raw`.log
        env = dict(os.environ, REFEREE_BEHAVE_FILE=raw)
        with open(raw + ".log", "w") as out:
            p = subprocess.run(["lake", "env", "lean", f"-M{os.environ.get('REFEREE_MEM', '8192')}",
                                os.path.basename(path)], cwd=project, stdout=out, stderr=subprocess.STDOUT, env=env)
    finally:
        os.unlink(path)
    errs = [ln for ln in open(raw + ".log", errors="replace") if ": error" in ln]
    if p.returncode != 0 and not errs:
        errs = [f"lean exited {p.returncode}"]
    return errs


def main(argv):
    opts = dict(a[2:].split("=", 1) for a in argv if a.startswith("--") and "=" in a)
    project, out = os.path.abspath(opts["project"]), os.path.abspath(opts["out"])
    os.makedirs(out, exist_ok=True)
    rows = BR.read_rows(opts["rows"])
    imports = opts.get("imports", "").split(",")
    phase = opts.get("phase", "all")
    rows_raw, pairs_raw = os.path.join(out, "rows.raw"), os.path.join(out, "pairs.raw")
    if phase in ("rows", "all"):
        errs = run(project, check_file(imports, ["#referee_behave_rows " + " ".join(r["def"] for r in rows)]), rows_raw)
        print(f"BEHAVIOUR\trows\t{rows_raw}" + (f"\terrors: {' | '.join(e.strip() for e in errs[:5])}" if errs else ""))
        if errs:
            return 1
    if phase in ("pairs", "all"):
        shapes, _, _ = BR.parse(rows_raw)
        swap, fam = BR.control_pairs(rows, shapes)
        todo = sorted(set(swap) | set(fam))
        errs = run(project, check_file(imports, ["#referee_behave_pairs " + " ".join(f"{d} {n}" for d, n in todo)]), pairs_raw)
        print(f"BEHAVIOUR\tpairs\t{len(todo)}\t{pairs_raw}" +
              (f"\terrors: {' | '.join(e.strip() for e in errs[:5])}" if errs else ""))
        if errs:
            return 1
    return BR.main([f"--rows={opts['rows']}", f"--raw={rows_raw}", f"--out={out}"] +
                   ([f"--pairs-raw={pairs_raw}"] if os.path.exists(pairs_raw) else []))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
