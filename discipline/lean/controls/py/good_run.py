import sys
THRESH = 3  # source: declared prediction of section V1
def verdict(name, ok, detail):
    print(name, "HOLDS" if ok else "FAILS", detail)
def control(name, ok):
    print(name, "control", "FAILS as it must" if not ok else "PASSED: broken")
vals = [int(a) for a in sys.argv[1:]] or [4, 5]
verdict("V1", min(vals) >= THRESH, "every value at least the threshold")
control("V1-ctrl", min([v - 10 for v in vals]) >= THRESH)
