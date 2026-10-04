"""Find a preimage of a small black-and-white picture under the example rule B,
using the row-by-row construction from the proof (top row first).

Pixel (i, j): i = column (to the right), j = row (upwards).
Rule: out(i,j) = f(a,b,c,d,e) with a=x(i,j), b=x(i+1,j), c=x(i+2,j), d=x(i+3,j), e=x(i,j+1).
"""

def g(s, b, c, d):
    if s == 0:
        return (1 - c) if b else (c | d)
    return ((1 - c) & (1 - d)) if b else c

def f(a, b, c, d, e):
    return g(a ^ e, b, c, d)

TT = sum(f(n & 1, n >> 1 & 1, n >> 2 & 1, n >> 3 & 1, n >> 4 & 1) << n for n in range(32))
assert TT == 0x3A3C353C

def solve_row(e, y):
    """Row r of length len(y)+3 with f(r[i..i+3], e[i]) == y[i] for all i (DFS)."""
    n = len(y)
    def dfs(r):
        i = len(r) - 3
        if i == n:
            return r
        for d in (0, 1):
            if f(r[i], r[i + 1], r[i + 2], d, e[i]) == y[i]:
                res = dfs(r + [d])
                if res:
                    return res
        return None
    for start in range(8):
        res = dfs([start & 1, start >> 1 & 1, start >> 2 & 1])
        if res:
            return res
    raise AssertionError("no row solution (would contradict the row lemma)")

def preimage(target):
    """target[j][i], j = 0 is the bottom row. Returns x[j][i] of size (H+1) x (W+3)."""
    H, W = len(target), len(target[0])
    x = [None] * (H + 1)
    x[H] = [0] * (W + 3)                       # the row above the picture: anything
    for j in range(H - 1, -1, -1):             # top down
        x[j] = solve_row(x[j + 1][:W], target[j])
    return x

def apply(x, H, W):
    return [[f(x[j][i], x[j][i + 1], x[j][i + 2], x[j][i + 3], x[j + 1][i]) for i in range(W)]
            for j in range(H)]

def show(rows):
    for row in reversed(rows):                 # print the top row first
        print("".join("#" if v else "." for v in row))

if __name__ == "__main__":
    picture = [                                # drawn top row first
        ".#...#.",
        ".......",
        "#.....#",
        ".#####.",
    ]
    target = [[1 if ch == "#" else 0 for ch in row] for row in reversed(picture)]
    H, W = len(target), len(target[0])
    x = preimage(target)
    print("target (%dx%d):" % (W, H)); show(target)
    print("preimage (%dx%d):" % (W + 3, H + 1)); show(x)
    assert apply(x, H, W) == target
    print("check: F(preimage) == target on the picture: OK")
