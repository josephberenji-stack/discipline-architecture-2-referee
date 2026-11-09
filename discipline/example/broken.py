"""
broken.py -- the negative control for the suite: a file the referee must refuse.
"""
import sys
sys.path.insert(0, "discipline")
import referee as R
R.declare("B1", predicts="something holds", kills="it does not")
R.verdict("B1", True, "this verdict was typed, not computed")
R.close()
