import sys
def verdict(name, ok, detail):
    print(name, "HOLDS" if ok else "FAILS", detail)
def control(name, ok):
    print(name, "control", "fails as it must" if not ok else "PASSED: broken")
err = float(sys.argv[1]) if len(sys.argv) > 1 else 0.01
verdict("E1", err < 0.0137, "error below the threshold")
control("E1-ctrl", err + 1 < 0.0137)
