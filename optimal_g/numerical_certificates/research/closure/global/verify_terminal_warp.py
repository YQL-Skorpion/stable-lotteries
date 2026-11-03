"""Exact conditional terminal-curvature certificate; standard library only.

This does not certify that the exact optimizer lies in the parameter box.
It proves -d_S^2 log(M0-S-B(zstar-(S-Sstar),q,S)) > 350
throughout the displayed rational box, with M0=Sstar+3/25.
"""
from fractions import Fraction as F
import argparse
import json

NVAR = 5
ZERO = (0,) * NVAR


class Poly:
    def __init__(self, value=0):
        self.c = value if isinstance(value, dict) else {ZERO: F(value)}
        self.c = {m: c for m, c in self.c.items() if c}

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        ans = dict(self.c)
        for m, c in other.c.items():
            ans[m] = ans.get(m, F(0)) + c
        return Poly(ans)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.c.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -F(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        ans = {}
        for m, c in self.c.items():
            for n, d in other.c.items():
                mn = tuple(a + b for a, b in zip(m, n))
                ans[mn] = ans.get(mn, F(0)) + c * d
        return Poly(ans)

    __rmul__ = __mul__

    def derivative(self, index):
        ans = {}
        for m, c in self.c.items():
            if m[index]:
                n = list(m)
                n[index] -= 1
                ans[tuple(n)] = c * m[index]
        return Poly(ans)

    def enclosure(self):
        center = self.c.get(ZERO, F(0))
        radius = sum((abs(c) for m, c in self.c.items() if m != ZERO), F(0))
        return center - radius, center + radius


names = ['L', 'q', 'zstar', 'Sstar', 'S']
boxes = [
    ('.562325', '.56233'),
    ('.2700', '.2703'),
    ('.8622', '.8626'),
    ('.0230', '.0231'),
    ('.0219728', '.0266504'),
]
variables = []
radii = []
for index, (lo, hi) in enumerate(boxes):
    lo, hi = F(lo), F(hi)
    radius = (hi - lo) / 2
    unit = [0] * NVAR
    unit[index] = 1
    variables.append(Poly({ZERO: (lo + hi) / 2, tuple(unit): radius}))
    radii.append(radius)

L, q, zstar, Sstar, S = variables
z = zstar - (S - Sstar)
d = 1 - z + q
Q = lambda t: L * t - F(1, 2) * t * t

parser = argparse.ArgumentParser()
parser.add_argument('--constant-m0', default=None,
                    help='Use this exact constant M0 instead of Sstar+3/25.')
parser.add_argument('--curvature', default='350')
args = parser.parse_args()
M0 = Sstar + F(3, 25) if args.constant_m0 is None else Poly(F(args.constant_m0))
curvature = F(args.curvature)

# Zscaled=(L-q)(1-q) Zbar. This positive scale is independent of S.
Zscaled = (L - q) * (1 - q) * (M0 - S) - z * (
    (1 - q) * (Q(d) - S) - L * Q(1 - q) + L * S
)
Zs = Zscaled.derivative(4) * (1 / radii[4])
Zss = Zs.derivative(4) * (1 / radii[4])
curvature_numerator = Zs * Zs - Zscaled * Zss - curvature * Zscaled * Zscaled

answer = {'box': dict(zip(names, boxes)),
          'M0': args.constant_m0 or 'Sstar+3/25',
          'certified_curvature_lower_bound': str(curvature)}
for name, poly in [('Zscaled', Zscaled), ('negative_Zs', -Zs),
                   ('curvature_numerator', curvature_numerator)]:
    lo, hi = poly.enclosure()
    assert lo > 0, (name, lo)
    answer[name] = {'terms': len(poly.c), 'lower_exact': str(lo),
                    'upper_exact': str(hi), 'lower': float(lo), 'upper': float(hi)}

print(json.dumps(answer, indent=2))
