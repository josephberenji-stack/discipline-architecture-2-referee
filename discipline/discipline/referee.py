"""referee.py -- the runtime half of the referee.  The author writes the file; this module
refuses the moves the author is not allowed to make.

WHY.  A file that both computes a result and announces whether the result came out is a file
in which the announcing party had an interest in the answer.  The failures this produces are
not lies; they are a verdict typed rather than computed, a prediction that failed with no
line saying so, and a withdrawal printed below the result it withdraws.  Each of those is the
author writing the referee's line.  This module makes those lines un-writable:

  declare(name, predicts=..., kills=..., requires=[...], control=..., budget=...)
      must precede verdict(name, ...).  A verdict with no declaration is refused.
      'predicts' and 'kills' are strings the run will be held to; 'requires' lists the
      existing results the claim leans on, by file and line; 'budget' records which
      formulation this is, out of how many.
  verdict(name, ok, detail)
      'ok' must be an EXPRESSION, not a literal -- the call site is parsed and
      `verdict("X", True, ...)` is refused.  The printed word is chosen by the value,
      never typed.
  control(name, ok, detail, vacuous=, rows=)
      a negative control: a case that MUST fail.  ok == True is a failure of the file,
      not a pass.  At least one is required before close().  `vacuous` states how many of
      the control's rows agree with the claim by construction and are therefore silent
      rather than failing; omitting it is recorded as NOT MEASURED so the omission is on
      the page.
  rows(name, violating)
      the rows behind a count.  A verdict whose 'ok' came from a count should call rows()
      with the offending items; close() lists sections that reported a number and no rows.
  withdraw(name, text)
      prints a withdrawal and refuses to run after a verdict for the same name has been
      printed -- withdrawals go above results.
  close()
      prints the ledger of declarations against outcomes and exits non-zero when any
      verdict lacked a declaration, no control ran, a control passed, or a prediction was
      contradicted without the file saying so.

Rows, not counts.  Predictions before runs.  The verdict is computed.
"""
import ast, inspect, sys

_decl, _out, _ctrl, _rows, _withdrawn, _errors = {}, {}, {}, {}, set(), []
_vac = {}


def declare(name, predicts, kills, requires=(), control=None, budget="1 of 3"):
    if name in _out:
        _errors.append(f"{name}: declared after its verdict -- declarations come first")
    _decl[name] = dict(predicts=predicts, kills=kills, requires=list(requires),
                       control=control, budget=budget)
    print(f"  [{name}] DECLARED  predicts: {predicts}")
    print(f"  [{name}]           kills:    {kills}")
    if requires:
        print(f"  [{name}]           requires: {', '.join(requires)}")
    if control:
        print(f"  [{name}]           control:  {control}")
    print(f"  [{name}]           budget:   formulation {budget}")


def _arg_is_literal(depth=2):
    """parse the caller's call site; True if the second positional argument is a constant."""
    frame = inspect.stack()[depth]
    src = "".join(inspect.getframeinfo(frame.frame).code_context or [])
    try:
        tree = ast.parse(src.strip())
    except SyntaxError:
        # multi-line call: read forward until it parses
        # for a module the first line is reported as 0, not 1; reading from 0 would start one line late
        lines, first = inspect.getsourcelines(frame.frame)
        start = frame.lineno - (first or 1)
        for end in range(start + 1, min(start + 12, len(lines)) + 1):
            try:
                tree = ast.parse("".join(lines[start:end]).strip()); break
            except SyntaxError:
                continue
        else:
            return False
    for node in ast.walk(tree):
        # the call may be bare (`verdict(...)`) or through the module (`R.verdict(...)`)
        fn = getattr(node.func, "id", None) or getattr(node.func, "attr", "") \
            if isinstance(node, ast.Call) else ""
        if isinstance(node, ast.Call) and fn in ("verdict", "control"):
            args = node.args
            if len(args) >= 2 and isinstance(args[1], ast.Constant):
                return True
            for kw in node.keywords:
                if kw.arg == "ok" and isinstance(kw.value, ast.Constant):
                    return True
    return False


def verdict(name, ok, detail=""):
    if _arg_is_literal():
        _errors.append(f"{name}: verdict argument is a literal -- the verdict must be computed")
        print(f"  {name} REFUSED.  literal verdict.  {detail}")
        return
    if name not in _decl:
        _errors.append(f"{name}: verdict with no declaration")
        print(f"  {name} REFUSED.  no declaration.  {detail}")
        return
    ok = bool(ok)
    _out[name] = ok
    word = "HOLDS" if ok else "FAILS"
    print(f"  {name} {word}.  {detail}")
    if not ok:
        print(f"  [{name}] the prediction was: {_decl[name]['predicts']}")
        print(f"  [{name}] the kill condition was: {_decl[name]['kills']}")


def control(name, ok, detail="", vacuous=None, rows=None):
    """vacuous: how many of this control's rows AGREE with the claim, by construction or by
    arithmetic, and are therefore silent rather than failing; rows: how many it was scored
    on.  A control that agrees on part of its grid is not failing there, and the referee
    sees only pass or fail, so the count has to be stated.  Passing vacuous=0 is a claim
    that none of its rows are silent; omitting it is recorded as NOT MEASURED."""
    if _arg_is_literal():
        _errors.append(f"{name}: control argument is a literal")
        print(f"  control {name} REFUSED.  literal.")
        return
    ok = bool(ok)
    _ctrl[name] = ok
    _vac[name] = (vacuous, rows)
    if ok:
        _errors.append(f"{name}: negative control PASSED -- the check cannot fail")
        print(f"  control {name}: PASSED -- this is a failure of the file.  {detail}")
    else:
        print(f"  control {name}: fails as it must.  {detail}")
    if vacuous is None:
        print(f"  control {name}: vacuity NOT MEASURED")
    else:
        of = f" of {rows}" if rows else ""
        print(f"  control {name}: silent on {vacuous}{of} rows")


def rows(name, violating, show=8):
    _rows[name] = list(violating)
    if not violating:
        print(f"  [{name}] 0 violating rows (of the examined set; see the section's count line)")
        return
    print(f"  [{name}] {len(violating)} violating rows; first {min(show, len(violating))}:")
    for r in list(violating)[:show]:
        print(f"      {r}")


def withdraw(name, text):
    if name in _out:
        _errors.append(f"{name}: withdrawal printed BELOW its result -- move it above")
    _withdrawn.add(name)
    print(f"  WITHDRAWN [{name}]: {text}")


def close():
    print()
    print("  ============================== referee ==============================")
    for name, d in _decl.items():
        res = _out.get(name)
        word = "HOLDS" if res else ("FAILS" if res is False else "NO VERDICT")
        print(f"  {name:>8}  {word:<10} predicted: {d['predicts']}")
        if res is False:
            print(f"  {'':>8}  the formulation failed; budget was {d['budget']}.  "
                  f"Next: a new formulation or the human's argument for a new question.")
    if not _ctrl:
        _errors.append("no negative control ran")
    counted = [n for n in _out if n not in _rows]
    if counted:
        print(f"  sections with a verdict and no rows() call: {', '.join(counted)}")
    if _errors:
        print("  REFEREE: the run does not count.  Reasons:")
        for e in _errors:
            print(f"    - {e}")
        sys.exit(1)
    held = sum(1 for v in _out.values() if v)
    unmeasured = [n for n, (v, _) in _vac.items() if v is None]
    silent = [n for n, (v, _) in _vac.items() if v]
    print(f"  REFEREE: {held} of {len(_out)} declared claims hold; "
          f"{len(_ctrl)} control(s) failed as required.  The run counts.")
    if unmeasured:
        print(f"  REFEREE: vacuity NOT MEASURED on {len(unmeasured)} control(s): "
              f"{', '.join(unmeasured)}")
    if silent:
        print(f"  REFEREE: {len(silent)} control(s) silent on some rows: "
              f"{', '.join(silent)}")
    return 0
