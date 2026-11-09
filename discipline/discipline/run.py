"""run.py -- run every check with each one scoped correctly.  Rows, not counts.

    python3 -m discipline.run FILE_OR_DIR [...] [--names NAMES.md]
                              [--corpus ROOT ...] [--floor=N] [--baseline=2,3,...]

Eleven checks are FILE-LEVEL and run on the paths you give.  Two -- `ledger` and `rollover`
-- are CORPUS-LEVEL: they need the roots where the correction numbering and the working
documents live, given with --corpus.  Without --corpus they are skipped and say so, rather
than reporting every number below one file's highest as a gap.

A check with a standing backlog cannot signal a new violation, so if a baseline of standing
rows is on record (registers/BASELINE.md) every file-level check's output is split into
HELD and NEW, the new rows are printed by name, and the exit code is the NEW count.  The
backlog is still printed under its check and is not cleared by this.  The full output of
every check is written to discipline-report.md beside the run.
"""
import sys, io, contextlib, os
from pathlib import Path
import sys as _s, os as _o; _s.path.insert(0, _o.path.dirname(_o.path.abspath(__file__)))
import predeclare, rowsplit, guard, withdraw, ledger, noliteral, names, forced, cited
import ground, primitive, reprleak, baseline, rollover, config

FILE_LEVEL = ["predeclare", "rowsplit", "guard", "withdraw", "noliteral", "names",
              "forced", "cited", "ground", "primitive", "reprleak"]


def main(argv):
    reg, corpus, ledger_opts = None, [], []
    argv = list(argv)
    if "--names" in argv:
        i = argv.index("--names"); reg = argv[i + 1]; del argv[i:i + 2]
    while "--corpus" in argv:
        i = argv.index("--corpus"); corpus.append(argv[i + 1]); del argv[i:i + 2]
    for a in list(argv):
        if a.startswith(("--max=", "--floor=", "--baseline=")):
            ledger_opts.append(a); argv.remove(a)
    if corpus:
        # the corpus-level checks and the citation check share one notion of the roots
        os.environ["DISCIPLINE_ROOTS"] = os.pathsep.join(
            str(Path(c).resolve()) for c in corpus)
    if reg is None:
        cand = config.registers(argv[0] if argv else None) / "NAMES.md"
        reg = str(cand) if cand.is_file() else None

    checks = [("predeclare", lambda: predeclare.check(argv)),
              ("rowsplit", lambda: rowsplit.lint(argv)),
              ("guard", lambda: guard.lint(argv)),
              ("withdraw", lambda: withdraw.check(argv)),
              ("noliteral", lambda: noliteral.main(argv)),
              ("names", lambda: names.main((["--names", reg] if reg else []) + argv)),
              ("forced", lambda: forced.check(argv)),
              ("cited", lambda: cited.check(argv)),
              ("ground", lambda: ground.check(argv)),
              ("primitive", lambda: primitive.check(argv)),
              ("reprleak", lambda: reprleak.check(argv)),
              ("ledger", lambda: ledger.main(ledger_opts + (corpus or argv))),
              ("rollover", lambda: rollover.check(corpus or argv))]

    held_set = baseline.load()
    report, total, file_rows, new_rows = ["# discipline report", ""], 0, 0, 0
    new_detail = []
    for title, fn in checks:
        if title in ("ledger", "rollover") and not corpus:
            print(f"== {title}: skipped (corpus-level; pass --corpus ROOT)")
            report += [f"## {title} — skipped", "",
                       "corpus-level check; pass --corpus ROOT", ""]
            continue
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            res = fn()
        n = len(res) if hasattr(res, "__len__") else int(res)
        total += n
        if title in FILE_LEVEL:
            file_rows += n
        if title in FILE_LEVEL:
            held, new = baseline.split(title, buf.getvalue(), held_set)
            new_rows += len(new)
            new_detail += new
            print(f"== {title}: {n} rows ({len(held)} held, {len(new)} new)"
                  if held_set else f"== {title}: {n} rows")
        else:
            print(f"== {title}: {n} rows")
        report += [f"## {title} — {n} rows", "", "```", buf.getvalue().rstrip(), "```", ""]
    Path("discipline-report.md").write_text("\n".join(report))
    if held_set:
        print(f"\n  NEW rows, not on the baseline: {new_rows}")
        for k in new_detail[:20]:
            print("      %s | %s | %s | %s" % k)
    print(f"  discipline: {file_rows} file-level rows"
          f"{f' ({file_rows - new_rows} held by baseline)' if held_set else ''}"
          f"{f', {total - file_rows} corpus-level rows' if corpus else ''}"
          f"; report in discipline-report.md")
    return new_rows if held_set else total


if __name__ == "__main__":
    sys.exit(1 if main(sys.argv[1:]) else 0)
