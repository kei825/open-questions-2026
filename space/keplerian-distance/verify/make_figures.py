#!/usr/bin/env python3
"""Table of the 12 critical points and the two figures (orbits.svg, torus.svg).

Presentation only: floating point / mpmath are used here for drawing and for printing digits.
The rigorous statements are in sturm_count.py, krawczyk_torus.py and KeplerianDistance.lean.
Input: roots.txt written by sturm_count.py.
"""
import base64, os, struct, zlib
from fractions import Fraction as Fr
import mpmath as mp
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)
mp.mp.dps = 40
p1, e1, p2, e2 = mp.mpf(1), mp.mpf(493) / 500, mp.mpf(113) / 500, mp.mpf(4983) / 5000
w = 2 * mp.atan(mp.mpf(89) / 4000)

def X(f, p, e, om):
    r = p / (1 + e * mp.cos(f)); return (r * mp.cos(f + om), r * mp.sin(f + om))
def d2(f1, f2):
    a = X(f1, p1, e1, 0); b = X(f2, p2, e2, w); return (a[0] - b[0])**2 + (a[1] - b[1])**2
def ecc(f, e):  # eccentric anomaly in [0, 2pi)
    return mp.atan2(mp.sqrt(1 - e**2) * mp.sin(f), e + mp.cos(f)) % (2 * mp.pi)

pts = []
for line in open(os.path.join(HERE, "roots.txt")):
    kind, a, b = line.split()
    a, b = Fr(a), Fr(b); tm = (a + b) / 2
    t = mp.mpf(tm.numerator) / tm.denominator
    f1 = 2 * mp.atan(t)
    if kind == "F":
        al = mp.sin(w - f1) + e1 * mp.sin(w); be = mp.cos(w - f1) + e1 * mp.cos(w)
        mu = p1 * e1 * e2 * mp.sin(f1)
        de = p1 * e1 * mp.sin(f1) + p2 * e2 * (1 + e1 * mp.cos(f1)) * al
        c2 = -de / mu; s2 = -al * (c2 + e2) / be; f2 = mp.atan2(s2, c2)
    else:
        f2 = f1 - w
    h11 = mp.diff(lambda x, y: d2(x, y), (f1, f2), (2, 0))
    h12 = mp.diff(lambda x, y: d2(x, y), (f1, f2), (1, 1))
    h22 = mp.diff(lambda x, y: d2(x, y), (f1, f2), (0, 2))
    det = h11 * h22 - h12**2
    typ = "saddle" if det < 0 else ("minimum" if h11 > 0 else "maximum")
    dd = mp.sqrt(abs(d2(f1, f2))) if kind == "F" else mp.mpf(0)
    pts.append(dict(kind=kind, f1=f1, f2=f2, u1=ecc(f1, e1), u2=ecc(f2, e2), d=dd, typ=typ,
                    P=X(f1, p1, e1, 0), Q=X(f2, p2, e2, w)))
pts.sort(key=lambda r: (r["d"], r["f1"]))
for i, r in enumerate(pts, 1):
    r["n"] = i

deg = lambda x: mp.nstr(mp.degrees(x), 10, min_fixed=-1, max_fixed=4)
lines = ["| # | type | intersection? | f₁ (deg) | f₂ (deg) | u₁ (deg) | u₂ (deg) | d |",
         "|---|---|---|---|---|---|---|---|"]
for r in pts:
    f1d = mp.degrees(r["f1"]); f2d = mp.degrees(r["f2"])
    f2d = (f2d + 180) % 360 - 180
    lines.append(f"| {r['n']} | {r['typ']} | {'yes' if r['kind'] == 'I' else 'no'} | "
                 f"{mp.nstr(f1d, 10)} | {mp.nstr(f2d, 10)} | {mp.nstr(mp.degrees(r['u1']), 10)} | "
                 f"{mp.nstr(mp.degrees(r['u2']), 10)} | {'0' if r['kind'] == 'I' else mp.nstr(r['d'], 10)} |")
table = "\n".join(lines)
print(table)

# ----------------------------------------------------------------------------- orbits.svg
COL = {"minimum": "#1f9d55", "maximum": "#d64545", "saddle": "#7b4bc4"}
O1, O2 = "#2563a8", "#d9822b"
def orbit_xy(p, e, om, n=4000):
    f = np.linspace(-np.pi, np.pi, n)
    r = float(p) / (1 + float(e) * np.cos(f))
    return r * np.cos(f + float(om)), r * np.sin(f + float(om))
o1 = orbit_xy(p1, e1, 0); o2 = orbit_xy(p2, e2, w)

def panel(x0, y0, W, H, xr, yr, title, labels=True, labelset=None, marker_scale=1.0):
    """returns svg group for a panel mapping data box xr x yr to pixel box (equal aspect)."""
    sx = W / (xr[1] - xr[0]); sy = H / (yr[1] - yr[0]); s = min(sx, sy)
    cx = (xr[0] + xr[1]) / 2; cy = (yr[0] + yr[1]) / 2
    def P(x, y): return (x0 + W / 2 + (x - cx) * s, y0 + H / 2 - (y - cy) * s)
    g = [f'<g><rect x="{x0}" y="{y0}" width="{W}" height="{H}" fill="#fbfbfd" stroke="#bbb"/>',
         f'<clipPath id="c{x0}_{y0}"><rect x="{x0}" y="{y0}" width="{W}" height="{H}"/></clipPath>',
         f'<g clip-path="url(#c{x0}_{y0})">']
    for (xs, ys), col, dash in ((o1, O1, ""), (o2, O2, ' stroke-dasharray="7 4"')):
        pth = " ".join(f"{a:.2f},{b:.2f}" for a, b in (P(x, y) for x, y in zip(xs, ys)))
        g.append(f'<polyline points="{pth}" fill="none" stroke="{col}" stroke-width="2"{dash}/>')
    fx, fy = P(0, 0)
    g.append(f'<circle cx="{fx:.1f}" cy="{fy:.1f}" r="4" fill="#222"/>')
    for r in pts:
        (ax, ay), (bx, by) = P(float(r["P"][0]), float(r["P"][1])), P(float(r["Q"][0]), float(r["Q"][1]))
        col = COL[r["typ"]]
        if r["kind"] == "F":
            g.append(f'<line x1="{ax:.1f}" y1="{ay:.1f}" x2="{bx:.1f}" y2="{by:.1f}" stroke="{col}" '
                     f'stroke-width="2"/>')
            for (qx, qy) in ((ax, ay), (bx, by)):
                g.append(f'<circle cx="{qx:.1f}" cy="{qy:.1f}" r="{3.2*marker_scale}" fill="{col}"/>')
        else:
            g.append(f'<circle cx="{ax:.1f}" cy="{ay:.1f}" r="{5*marker_scale}" fill="none" stroke="{col}" '
                     f'stroke-width="2.2"/>')
        if labels and (labelset is None or r["n"] in labelset):
            lx, ly = (ax + bx) / 2, (ay + by) / 2
            dx, dy = LABEL_OFF.get((title[:1], r["n"]), (6, -6))
            g.append(f'<text x="{lx + dx:.1f}" y="{ly + dy:.1f}" font-size="13" fill="{col}" '
                     f'font-weight="bold">{r["n"]}</text>')
    g.append('</g>')
    g.append(f'<text x="{x0 + 8}" y="{y0 + 18}" font-size="14" fill="#222">{title}</text>')
    # scale bar
    L = 10 ** np.floor(np.log10((xr[1] - xr[0]) / 4))
    bx0, by0 = x0 + W - 20 - L * s, y0 + H - 14
    g.append(f'<line x1="{bx0:.1f}" y1="{by0}" x2="{bx0 + L*s:.1f}" y2="{by0}" stroke="#222" stroke-width="2"/>')
    g.append(f'<text x="{bx0:.1f}" y="{by0 - 5}" font-size="11" fill="#222">{L:g} (p₁ = 1)</text>')
    g.append('</g>')
    return "\n".join(g)

LABEL_OFF = {("A", 11): (8, 16), ("A", 12): (8, -8), ("A", 5): (6, -4), ("A", 9): (6, 4), ("A", 10): (6, 4),
             ("C", 4): (6, -6)}
Wt = 980
svg = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{Wt}" height="820" viewBox="0 0 {Wt} 820" '
       f'font-family="Helvetica, Arial, sans-serif">',
       f'<rect width="{Wt}" height="820" fill="white"/>']
svg.append(panel(10, 10, 960, 230, (-73.5, 3.5), (-8, 8),
                 "A. Whole orbits (equal scales). Focus = black dot. Points 1-3 and 6-8 are labelled in B.",
                 labelset={5, 9, 10, 11, 12}))
svg.append(panel(10, 255, 640, 500, (-72.5, -52.5), (-8, 8),
                 "B. Zoom near the apocentres", labelset={1, 2, 3, 6, 7, 8}))
svg.append(panel(665, 255, 305, 300, (-0.15, 0.75), (-0.45, 0.45), "C. Zoom near the focus", labelset={4}))
# legend
lx, ly = 670, 575
leg = [(O1, "orbit 1: p₁ = 1, e₁ = 493/500", "solid"),
       (O2, "orbit 2: p₂ = 113/500, e₂ = 4983/5000,", "dash")]
for i, (c, txt, st) in enumerate(leg):
    y = ly + 22 * i
    svg.append(f'<line x1="{lx}" y1="{y}" x2="{lx+30}" y2="{y}" stroke="{c}" stroke-width="2.5"'
               f'{" stroke-dasharray=\"7 4\"" if st == "dash" else ""}/>')
    svg.append(f'<text x="{lx+38}" y="{y+4}" font-size="11.5" fill="#222">{txt}</text>')
svg.append(f'<text x="{lx+38}" y="{ly+40}" font-size="11.5" fill="#222">pericentre turned by ω, tan(ω/2) = 89/4000</text>')
items = [("minimum", "local minimum (segment joins the two points)"), ("maximum", "local maximum"),
         ("saddle", "saddle point")]
for i, (k, txt) in enumerate(items):
    y = ly + 66 + 22 * i
    svg.append(f'<line x1="{lx}" y1="{y}" x2="{lx+30}" y2="{y}" stroke="{COL[k]}" stroke-width="2"/>'
               f'<circle cx="{lx}" cy="{y}" r="3.2" fill="{COL[k]}"/><circle cx="{lx+30}" cy="{y}" r="3.2" fill="{COL[k]}"/>')
    svg.append(f'<text x="{lx+38}" y="{y+4}" font-size="11.5" fill="#222">{txt}</text>')
y = ly + 66 + 66
svg.append(f'<circle cx="{lx+15}" cy="{y}" r="5" fill="none" stroke="{COL["minimum"]}" stroke-width="2.2"/>'
           f'<text x="{lx+38}" y="{y+4}" font-size="11.5" fill="#222">orbit intersection (minimum, d = 0)</text>')
svg.append(f'<text x="{lx}" y="{y+30}" font-size="11.5" fill="#222">Numbers = rows of the table in README.</text>')
svg.append(f'<text x="10" y="790" font-size="12" fill="#444">Each segment joins X₁(f₁) on orbit 1 to X₂(f₂) on orbit 2 '
           f'at a critical point of d²; at a non-intersection critical point it is perpendicular to both orbits.</text>')
svg.append('</svg>')
open(os.path.join(OUT, "orbits.svg"), "w").write("\n".join(svg))

# ----------------------------------------------------------------------------- torus.svg
N = 540
U0 = -np.pi / 2                                   # window u in [-90, 270) deg
u = U0 + (np.arange(N) + 0.5) * 2 * np.pi / N
U1, U2 = np.meshgrid(u, u, indexing="xy")          # x: u1, y: u2
a1 = float(p1 / (1 - e1**2)); a2 = float(p2 / (1 - e2**2))
b1 = a1 * np.sqrt(1 - float(e1)**2); b2 = a2 * np.sqrt(1 - float(e2)**2)
cw, sw = np.cos(float(w)), np.sin(float(w))
x1 = a1 * (np.cos(U1) - float(e1)); y1 = b1 * np.sin(U1)
X2 = a2 * (np.cos(U2) - float(e2)); Y2 = b2 * np.sin(U2)
x2 = cw * X2 - sw * Y2; y2 = sw * X2 + cw * Y2
D = np.sqrt((x1 - x2)**2 + (y1 - y2)**2)
L = np.log(D + 1e-3)
lv = (L - L.min()) / (L.max() - L.min())
anchors = np.array([[68, 1, 84], [59, 82, 139], [33, 145, 140], [94, 201, 98], [253, 231, 37]], float)
idx = lv * (len(anchors) - 1); i0 = np.clip(np.floor(idx).astype(int), 0, len(anchors) - 2); fr = idx - i0
img = anchors[i0] * (1 - fr[..., None]) + anchors[i0 + 1] * fr[..., None]
# contour lines of d at levels 0.5, 1, 2, 3, 5, 7, 10, 15, 20, 30, 40, 50, 60, 70
levels = np.array([0.25, 0.5, 1, 2, 3, 5, 7, 10, 15, 20, 30, 40, 50, 60, 70])
band = np.searchsorted(levels, D)
edge = (band != np.roll(band, 1, 0)) | (band != np.roll(band, 1, 1))
img[edge] = img[edge] * 0.35 + 255 * 0.65
img = img[::-1].astype(np.uint8)                   # row 0 = top = u2 = 360
def png(arr):
    h, w_ = arr.shape[:2]
    raw = b"".join(b"\x00" + arr[r].tobytes() for r in range(h))
    def chunk(t, d): return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xffffffff)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w_, h, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))
b64 = base64.b64encode(png(img)).decode()
ox, oy, S = 70, 40, 540
t = [f'<svg xmlns="http://www.w3.org/2000/svg" width="900" height="650" viewBox="0 0 900 650" '
     f'font-family="Helvetica, Arial, sans-serif">', '<rect width="900" height="650" fill="white"/>',
     f'<image x="{ox}" y="{oy}" width="{S}" height="{S}" href="data:image/png;base64,{b64}"/>',
     f'<rect x="{ox}" y="{oy}" width="{S}" height="{S}" fill="none" stroke="#222"/>',
     f'<text x="{ox}" y="25" font-size="15" fill="#222">Distance d on the torus of eccentric anomalies (u₁, u₂); '
     f'light lines = level curves</text>']
for k in range(-90, 271, 90):
    xx = ox + S * (k + 90) / 360; yy = oy + S - S * (k + 90) / 360
    t.append(f'<text x="{xx:.0f}" y="{oy + S + 18}" font-size="12" text-anchor="middle" fill="#222">{k}</text>')
    t.append(f'<text x="{ox - 8}" y="{yy + 4:.0f}" font-size="12" text-anchor="end" fill="#222">{k}</text>')
t.append(f'<text x="{ox + S/2}" y="{oy + S + 38}" font-size="13" text-anchor="middle" fill="#222">u₁ (deg), orbit 1</text>')
t.append(f'<text x="20" y="{oy + S/2}" font-size="13" fill="#222" transform="rotate(-90 20 {oy + S/2})" '
         f'text-anchor="middle">u₂ (deg), orbit 2</text>')
for r in pts:
    sh = lambda a: (float(a) - U0) % (2 * np.pi)
    xx = ox + S * sh(r["u1"]) / (2 * np.pi); yy = oy + S - S * sh(r["u2"]) / (2 * np.pi)
    if r["typ"] == "minimum":
        t.append(f'<circle cx="{xx:.1f}" cy="{yy:.1f}" r="6" fill="#4aa8ff" stroke="white" stroke-width="1.5"/>')
    elif r["typ"] == "maximum":
        t.append(f'<rect x="{xx-6:.1f}" y="{yy-6:.1f}" width="12" height="12" fill="#ff4d4d" stroke="white" stroke-width="1.5"/>')
    else:
        t.append(f'<path d="M{xx-6:.1f},{yy-6:.1f} L{xx+6:.1f},{yy+6:.1f} M{xx-6:.1f},{yy+6:.1f} L{xx+6:.1f},{yy-6:.1f}" '
                 f'stroke="white" stroke-width="4.5"/><path d="M{xx-6:.1f},{yy-6:.1f} L{xx+6:.1f},{yy+6:.1f} '
                 f'M{xx-6:.1f},{yy+6:.1f} L{xx+6:.1f},{yy-6:.1f}" stroke="#111" stroke-width="2.2"/>')
    t.append(f'<text x="{xx + 8:.1f}" y="{yy - 7:.1f}" font-size="13" font-weight="bold" fill="white" '
             f'stroke="#111" stroke-width="2.6" paint-order="stroke">{r["n"]}</text>')
lx = ox + S + 25
t.append(f'<circle cx="{lx+6}" cy="80" r="6" fill="#4aa8ff"/><text x="{lx+20}" y="84" font-size="13" fill="#222">minimum (4)</text>')
t.append(f'<rect x="{lx}" y="100" width="12" height="12" fill="#ff4d4d"/><text x="{lx+20}" y="111" font-size="13" fill="#222">maximum (2)</text>')
t.append(f'<path d="M{lx},{128} L{lx+12},{140} M{lx},{140} L{lx+12},{128}" stroke="#111" stroke-width="2.2"/>'
         f'<text x="{lx+20}" y="139" font-size="13" fill="#222">saddle (6)</text>')
t.append(f'<text x="{lx}" y="175" font-size="12" fill="#222">4 − 6 + 2 = 0 =</text>')
t.append(f'<text x="{lx}" y="191" font-size="12" fill="#222">Euler characteristic</text>')
t.append(f'<text x="{lx}" y="207" font-size="12" fill="#222">of the torus.</text>')
t.append(f'<text x="{lx}" y="240" font-size="12" fill="#222">Colour: log d</text>')
for i in range(5):
    c = anchors[i].astype(int)
    t.append(f'<rect x="{lx + 22*i}" y="250" width="22" height="12" fill="rgb({c[0]},{c[1]},{c[2]})"/>')
t.append(f'<text x="{lx}" y="278" font-size="11" fill="#222">small</text><text x="{lx+110}" y="278" '
         f'font-size="11" text-anchor="end" fill="#222">large</text>')
t.append(f'<text x="{lx}" y="310" font-size="11" fill="#222">Levels of d: 0.25, 0.5, 1, 2, 3,</text>')
t.append(f'<text x="{lx}" y="325" font-size="11" fill="#222">5, 7, 10, 15, 20, 30, …, 70</text>')
t.append(f'<text x="{lx}" y="355" font-size="11" fill="#222">Numbers = table rows.</text>')
t.append('</svg>')
open(os.path.join(OUT, "torus.svg"), "w").write("\n".join(t))
open(os.path.join(HERE, "table.md"), "w").write(table + "\n")
print("wrote orbits.svg, torus.svg, verify/table.md")
