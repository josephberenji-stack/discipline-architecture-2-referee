import sys
def verdict(name, ok, detail):
    print(name, "HOLDS" if ok else "FAILS", detail)
vals = [int(a) for a in sys.argv[1:]]
verdict("V1", sum(vals) > len(vals), "sum exceeds count")
