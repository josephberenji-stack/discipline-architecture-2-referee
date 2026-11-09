def f(xs):
    expected = [1, 0, 0, 140]
    result = [x * 2 for x in xs]
    return result == expected
