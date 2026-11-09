"""
example.py -- is the sum of the first n odd numbers a perfect square?

Human: "I think adding up odd numbers always gives you a square."

# MIRRORS.  The identity 1 + 3 + ... + (2n-1) = n^2 is a classical result; it is
# rebuilt here from the definition and nothing is imported for it.

DECLARED IN ADVANCE.  For every n from 1 to 200 the sum of the first n odd numbers is
the square of some integer.  KILL: an n in that range whose sum is not a square.
CONTROL: the sum of the first n EVEN numbers is a square -- which must FAIL, since
2 + 4 = 6 is not one.

THE OBJECTS.  An ODD NUMBER is 2k - 1 for k >= 1.  The SUM S(n) is the sum of the
first n of them.  A PERFECT SQUARE is an integer m*m for some integer m >= 0.

WHAT IS FORCED.  I looked for a theorem forcing the answer whatever the objects are:
the identity above forces it, and it is the thing being checked here, so the run is
a calibration of the code against a known result and is declared as such.
"""
import sys
sys.path.insert(0, "discipline")
import referee as R

R.declare("SQ1",
          predicts="for every n from 1 to 200 the sum of the first n odd numbers is a perfect square",
          kills="an n in 1..200 whose sum of the first n odd numbers is not a perfect square",
          requires=[],
          control="the sum of the first n even numbers is a perfect square, which must fail",
          budget="1 of 3")

def is_square(m):
    r = int(m ** 0.5)
    while r * r < m:
        r += 1
    while r * r > m:
        r -= 1
    return r * r == m

N = 200
bad = []
for n in range(1, N + 1):
    s = sum(2 * k - 1 for k in range(1, n + 1))
    if not is_square(s):
        bad.append((n, s))
R.rows("SQ1", bad)
R.verdict("SQ1", len(bad) == 0, f"{N - len(bad)} of {N} sums are squares")

even_bad = []
for n in range(1, N + 1):
    s = sum(2 * k for k in range(1, n + 1))
    if not is_square(s):
        even_bad.append((n, s))
# rows where the control agrees with the claim by arithmetic: n = 1 gives 2, not a square, so none
R.control("even-ctrl", len(even_bad) == 0,
          f"{len(even_bad)} of {N} even sums are not squares", vacuous=0, rows=N)
R.close()
