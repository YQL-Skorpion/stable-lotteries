"""verify.py -- checks the certificate for the upper bound  M(g*) <= 1 + 2*lambda = 2.1248.

Usage:  python3 verify.py             (Python 3 and NumPy; about 3 minutes)

certificate.json contains
  lambda         a rational, written as a string;
  phi            the score function phi*, a continuous piecewise polynomial: a list of pieces
                 {lo, hi, coeffs}, the value on [lo, hi] being sum_k coeffs[k] (r - lo)^k;
  coefficients   the data of beta(p) and of c(p, x) = [a(p) (lambda - x) + b(p) phi(x)]_+ for
                 p in [p0, p1], in three regimes of p (see `coefficients` below);
  box_range      p0, p1: the masses covered by the interval checks;
  landmarks      r1 < c < rc < zdep < pstar, piece boundaries used by the exact checks; in the
                 paper rc = r_- and zdep = z_+, and phi* = lambda - r on [rc, zdep];
  constants      m0, M (the Lipschitz constants of Lemma 11) and the partition of [0, lambda]
                 that reduces (25) near p = 1 to polynomial inequalities (Appendix B.2);
  box_options    subdivision parameters.

Part 1 decides, in exact rational arithmetic, every hypothesis on phi* in the Verifier Lemma
(Lemma 8) and in Lemma 11.  Part 2 verifies the four inequalities (37), (38) of the Verifier
Lemma for p in [p0, p1] by rigorous interval arithmetic on a subdivision of their domains.
Appendix B.2 of the paper says why these checks suffice.  Equation and lemma numbers refer to
the paper.
"""
import sys
import json
import time
import itertools
from fractions import Fraction as F
from math import comb
from pathlib import Path
import numpy as np


# ======================================================================================
# 1. Exact arithmetic on polynomials.  A polynomial inequality on an interval is decided from
#    the Bernstein coefficients of the polynomial on that interval, bisecting until every
#    coefficient has the required sign.  Since the Bernstein coefficients converge to the
#    values of the polynomial, this terminates whenever the polynomial has no zero in the
#    open interval (zeros at the endpoints are fine: the first and last coefficients are the
#    endpoint values).
# ======================================================================================

def poly_eval(c, t):
    acc = F(0)
    for a in reversed(c):
        acc = acc * t + a
    return acc


def poly_deriv(c):
    return [F(k) * c[k] for k in range(1, len(c))] or [F(0)]


def poly_integral(c, a, b):
    ci = [F(0)] + [c[k] / (k + 1) for k in range(len(c))]
    return poly_eval(ci, b) - poly_eval(ci, a)


def poly_shift_scale(c, a, b):
    """Power coefficients of s -> p(a + (b - a) s), s in [0, 1]."""
    h = b - a
    out = [F(0)] * len(c)
    for k in range(len(c)):
        for j in range(k + 1):
            out[j] += c[k] * comb(k, j) * a ** (k - j) * h ** j
    return out


def bernstein(c):
    n = len(c) - 1
    return [sum(c[j] * comb(k, j) / comb(n, j) for j in range(k + 1)) for k in range(n + 1)]


def subdivide(b):
    """de Casteljau split of Bernstein coefficients at 1/2."""
    left, right, cur = [b[0]], [b[-1]], list(b)
    for _ in range(len(b) - 1):
        cur = [(cur[i] + cur[i + 1]) / 2 for i in range(len(cur) - 1)]
        left.append(cur[0]); right.append(cur[-1])
    return left, list(reversed(right))


def poly_nonpositive(c, a, b, depth=60):
    """True if p <= 0 on [a, b] is proved (p has power coefficients c in the variable r)."""
    stack = [(bernstein(poly_shift_scale(c, F(a), F(b))), 0)]
    while stack:
        bc, d = stack.pop()
        if all(x <= 0 for x in bc):
            continue
        if bc[0] > 0 or bc[-1] > 0 or d >= depth:
            return False
        l, r = subdivide(bc)
        stack.append((l, d + 1)); stack.append((r, d + 1))
    return True


def poly_nonnegative(c, a, b):
    return poly_nonpositive([-x for x in c], a, b)


def poly_identically_zero(c):
    return all(x == 0 for x in c)


def pmul(x, y):
    out = [F(0)] * (len(x) + len(y) - 1)
    for i, xi in enumerate(x):
        for j, yj in enumerate(y):
            out[i + j] += xi * yj
    return out


def padd(x, y, s=1):
    n = max(len(x), len(y))
    return [(x[i] if i < len(x) else 0) + s * (y[i] if i < len(y) else 0) for i in range(n)]


# ======================================================================================
# 2. Rigorous interval arithmetic on NumPy arrays.  Every operation rounds its lower end down
#    and its upper end up by one unit in the last place.  Since IEEE-754 +, -, *, / are
#    correctly rounded, the exact result lies within one ulp of the computed one, so the
#    widened interval contains it.  This is the only floating-point fact the interval checks
#    rely on; all inputs are rationals enclosed by neighbouring floats (frac_bounds).
# ======================================================================================

def down(x):
    return np.nextafter(np.asarray(x, dtype=float), -np.inf)


def up(x):
    return np.nextafter(np.asarray(x, dtype=float), np.inf)


def frac_bounds(q):
    """The smallest float interval containing the rational q."""
    q = F(q); x = float(q); fx = F(x)
    lo = x if fx <= q else float(np.nextafter(x, -np.inf))
    hi = x if fx >= q else float(np.nextafter(x, np.inf))
    assert F(lo) <= q <= F(hi)
    return lo, hi


class I:
    """An array of closed intervals [lo, hi]."""
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        if hi is None:
            if isinstance(lo, I):
                self.lo, self.hi = lo.lo, lo.hi; return
            if isinstance(lo, F):
                a, b = frac_bounds(lo)
                self.lo, self.hi = np.asarray(a, float), np.asarray(b, float); return
            lo = np.asarray(lo, dtype=float)
            self.lo, self.hi = lo, lo.copy()
        else:
            self.lo, self.hi = np.asarray(lo, dtype=float), np.asarray(hi, dtype=float)

    @staticmethod
    def c(x):
        return x if isinstance(x, I) else I(x)

    def mag(self):
        return np.maximum(np.abs(self.lo), np.abs(self.hi))

    # binary operations return NotImplemented for a Dual so that Dual's reflected operation runs
    def __add__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        o = I.c(o); return I(down(self.lo + o.lo), up(self.hi + o.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        o = I.c(o); return I(down(self.lo - o.hi), up(self.hi - o.lo))

    def __rsub__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        return I.c(o) - self

    def __mul__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        o = I.c(o)
        p1, p2, p3, p4 = self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi
        return I(down(np.minimum(np.minimum(p1, p2), np.minimum(p3, p4))),
                 up(np.maximum(np.maximum(p1, p2), np.maximum(p3, p4))))

    __rmul__ = __mul__

    def reciprocal(self):
        assert np.all((self.lo > 0) | (self.hi < 0)), 'division by an interval containing zero'
        return I(down(1.0 / self.hi), up(1.0 / self.lo))

    def __truediv__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        return self * I.c(o).reciprocal()

    def __rtruediv__(self, o):
        if hasattr(o, 'grad'):
            return NotImplemented
        return I.c(o) * self.reciprocal()

    def pos(self):
        return I(np.maximum(self.lo, 0.0), np.maximum(self.hi, 0.0))

    def maximum(self, o):
        o = I.c(o); return I(np.maximum(self.lo, o.lo), np.maximum(self.hi, o.hi))

    def minimum(self, o):
        o = I.c(o); return I(np.minimum(self.lo, o.lo), np.minimum(self.hi, o.hi))

    def hull(self, o):
        o = I.c(o); return I(np.minimum(self.lo, o.lo), np.maximum(self.hi, o.hi))

    def bcast(self, shape):
        return I(np.broadcast_to(self.lo, shape).copy(), np.broadcast_to(self.hi, shape).copy())


class Piecewise:
    """A continuous piecewise polynomial on [0, 1] with rational knots and coefficients, stored
    as outer-rounded float intervals; piece j is sum_d C[j, d] (r - k_j)^d on [k_j, k_{j+1}]."""

    def __init__(self, knots, coeffs):
        n = len(knots) - 1
        deg = max(len(c) for c in coeffs)
        self.n, self.deg = n, deg
        self.klo = np.array([frac_bounds(k)[0] for k in knots])
        self.khi = np.array([frac_bounds(k)[1] for k in knots])
        self.Clo = np.zeros((n, deg)); self.Chi = np.zeros((n, deg))
        for j, c in enumerate(coeffs):
            for d, a in enumerate(c):
                self.Clo[j, d], self.Chi[j, d] = frac_bounds(a)

    def derivative(self):
        obj = Piecewise.__new__(Piecewise)
        obj.n, obj.klo, obj.khi = self.n, self.klo, self.khi
        if self.deg == 1:
            obj.Clo = np.zeros((self.n, 1)); obj.Chi = np.zeros((self.n, 1)); obj.deg = 1
            return obj
        d = np.arange(1, self.deg)
        obj.Clo = down(self.Clo[:, 1:] * d); obj.Chi = up(self.Chi[:, 1:] * d); obj.deg = self.deg - 1
        return obj

    def _horner(self, j, t):
        acc = I(self.Clo[j, -1], self.Chi[j, -1])
        for d in range(self.deg - 2, -1, -1):
            acc = acc * t + I(self.Clo[j, d], self.Chi[j, d])
        return acc

    def value(self, x):
        """Enclosure of the range over the interval array x (hull over the pieces x meets)."""
        x = I.c(x)
        shape = x.lo.shape
        j0 = np.clip(np.searchsorted(self.khi[1:], x.lo, side='left'), 0, self.n - 1)
        j1 = np.clip(np.searchsorted(self.klo[:-1], x.hi, side='right') - 1, 0, self.n - 1)
        out_lo = np.full(shape, np.inf); out_hi = np.full(shape, -np.inf)
        for s in range(int(np.max(j1 - j0)) + 1 if x.lo.size else 0):
            j = np.minimum(j0 + s, j1)
            active = (j0 + s) <= j1
            xlo = np.maximum(x.lo, self.klo[j]); xhi = np.minimum(x.hi, self.khi[j + 1])
            v = self._horner(j, I(down(xlo - self.khi[j]), up(xhi - self.klo[j])))
            out_lo = np.where(active, np.minimum(out_lo, v.lo), out_lo)
            out_hi = np.where(active, np.maximum(out_hi, v.hi), out_hi)
        return I(out_lo, out_hi)

    def point(self, x):
        return self.value(I(np.asarray(x, dtype=float)))

    def value_dec(self, x):
        """Enclosure [f(x.hi), f(x.lo)] for a function proved nonincreasing in Part 1."""
        return I(self.point(x.hi).lo, self.point(x.lo).hi)


# ======================================================================================
# 3. Values with gradient enclosures.  A Dual carries an enclosure of a quantity over a cell
#    and enclosures of its partial derivatives with respect to the cell coordinates.  For a
#    Lipschitz f the mean-value form  f(X) in f(centre) + grad f(X) . (X - centre)  holds with
#    any enclosure of the almost-everywhere gradient, which is what the chain rule below
#    produces (the derivative of [g]_+ is enclosed by [0, 1] g').
# ======================================================================================

class Dual:
    __slots__ = ('val', 'grad')

    def __init__(self, val, grad):
        self.val, self.grad = val, list(grad)

    @staticmethod
    def const(v, ndim, shape):
        z = I(np.zeros(shape))
        return Dual(I.c(v).bcast(shape), [z] * ndim)

    @staticmethod
    def var(v, k, ndim):
        v = I.c(v); shape = v.lo.shape
        g = [I(np.zeros(shape)) for _ in range(ndim)]
        g[k] = I(np.ones(shape))
        return Dual(v, g)

    def _c(self, o):
        return o if isinstance(o, Dual) else Dual.const(o, len(self.grad), self.val.lo.shape)

    def __add__(self, o):
        o = self._c(o); return Dual(self.val + o.val, [a + b for a, b in zip(self.grad, o.grad)])

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.val, [-a for a in self.grad])

    def __sub__(self, o):
        o = self._c(o); return Dual(self.val - o.val, [a - b for a, b in zip(self.grad, o.grad)])

    def __rsub__(self, o):
        return self._c(o) - self

    def __mul__(self, o):
        o = self._c(o)
        return Dual(self.val * o.val, [a * o.val + self.val * b for a, b in zip(self.grad, o.grad)])

    __rmul__ = __mul__

    def __truediv__(self, o):
        o = self._c(o); r = o.val.reciprocal(); q = self.val * r
        return Dual(q, [(a - q * b) * r for a, b in zip(self.grad, o.grad)])

    def pos(self):
        s = I(np.where(self.val.lo > 0, 1.0, 0.0), np.where(self.val.hi < 0, 0.0, 1.0))
        return Dual(self.val.pos(), [s * a for a in self.grad])

    def apply(self, f, df, mono=None):
        """Compose with a Piecewise f with derivative df; mono='dec' uses value_dec."""
        v = f.value_dec(self.val) if mono == 'dec' else f.value(self.val)
        d = df.value(self.val)
        return Dual(v, [d * a for a in self.grad])

    def apply_J(self, J, phi, lam_hi):
        """Compose with J (derivative phi), using that J increases below lambda and decreases
        above it, which Part 1 has verified."""
        x = self.val
        a = J.point(x.lo); b = J.point(x.hi)
        below, above = x.hi <= lam_hi, x.lo >= lam_hi
        lo = np.where(below, a.lo, np.where(above, b.lo, np.minimum(a.lo, b.lo)))
        hi = np.where(below, b.hi, np.where(above, a.hi, J.point(np.full(x.lo.shape, lam_hi)).hi))
        return Dual(I(lo, hi), [phi.value_dec(x) * g for g in self.grad])


# ======================================================================================
# 4. Subdivision.  verify(fun, cells) proves fun <= 0 on every cell: a cell is accepted when
#    the smaller of the two upper bounds (direct interval evaluation, mean-value form) is
#    nonpositive, and bisected otherwise, along the coordinate with the largest product of
#    gradient magnitude and width.
# ======================================================================================

def upper_bound(fun, cells, ndim):
    lo, hi = cells[:, :ndim], cells[:, ndim:]
    mid = (lo + hi) / 2
    f = fun(*[Dual.var(I(lo[:, k], hi[:, k]), k, ndim) for k in range(ndim)])
    fc = fun(*[Dual.var(I(mid[:, k], mid[:, k]), k, ndim) for k in range(ndim)])
    mv = fc.val
    for k in range(ndim):
        mv = mv + f.grad[k] * I(down(lo[:, k] - mid[:, k]), up(hi[:, k] - mid[:, k]))
    return np.minimum(f.val.hi, mv.hi), np.stack([g.mag() for g in f.grad], axis=1)


def verify(fun, cells, ndim, min_width, max_cells, batch, label):
    t0 = time.time()
    pending = np.asarray(cells, dtype=float)
    total, failed = 0, []
    while len(pending):
        cur, pending = pending[:batch], pending[batch:]
        ub, gm = upper_bound(fun, cur, ndim)
        total += len(cur)
        bad = ub > 0
        if not np.any(bad):
            continue
        cur, gm = cur[bad], gm[bad]
        widths = cur[:, ndim:] - cur[:, :ndim]
        tiny = np.all(widths < min_width, axis=1)
        if np.any(tiny):
            failed.append(cur[tiny]); cur, gm, widths = cur[~tiny], gm[~tiny], widths[~tiny]
        if not len(cur):
            continue
        k = np.argmax(gm * widths + 1e-300 * widths, axis=1)
        mid = (cur[:, :ndim] + cur[:, ndim:]) / 2
        left, right, rows = cur.copy(), cur.copy(), np.arange(len(cur))
        left[rows, ndim + k] = mid[rows, k]; right[rows, k] = mid[rows, k]
        pending = np.concatenate([pending, left, right])
        if total > max_cells:
            failed.append(pending); break
    ok = not failed
    print(f"  {label:<18} cells={total:>10} time={time.time() - t0:7.1f}s  "
          f"{'ok' if ok else 'UNRESOLVED ' + str(sum(len(x) for x in failed))}", flush=True)
    if failed:
        print('   sample unresolved cells:', failed[0][:3].tolist())
    return ok


def product_cells(p_cells, nsub, ndim):
    """Initial cells: each p-interval times a uniform nsub^(ndim-1) grid on [0, 1]^(ndim-1)."""
    g = np.linspace(0, 1, nsub + 1)
    out = []
    for plo, phi in p_cells:
        for idx in itertools.product(range(nsub), repeat=ndim - 1):
            out.append([plo] + [g[i] for i in idx] + [phi] + [g[i + 1] for i in idx])
    return np.array(out, dtype=float)


# ======================================================================================
# 5. The certificate and the four inequalities.
#
#    The inequalities of the Verifier Lemma, with delta_p(q) = J(1-p+q) - J(q),
#    K_p(q,z) = J(z-p+q) - J(z) - J(q), and W_x(y) = 0 for y <= lambda,
#    W_x(y) = lambda - y - r_x phi(y) for y > lambda, r_x = (lambda - x)/phi(x):
#
#      (39a)  q + beta delta_p(q) + c(p,x) <= lambda                      0 <= q <= min(p,x), x < lambda
#      (39b)  q + beta K_p(q,x) + c(p,x) <= 0                             0 <= q <= p <= x < lambda
#      (40a)  phi(x)[q + beta delta_p(q) + W_x(q) - lambda] <= [-phi(q)]_+ c(p,x)      0 <= q <= p
#      (40b)  phi(x)[q + beta K_p(q,z) + W_x(q) - W_x(z)] <= [-phi(z)]_+ c(p,x)       0 <= q <= p <= z <= 1
#
#    (40a), (40b) are checked divided by phi(x) > 0, with u_x = c(p,x)/phi(x) = [a r_x + b]_+.
#    On [rc, lambda), where phi(x) = lambda - x, one has r_x = 1 and u_x = [a + b]_+, so x
#    disappears: the families L3id, L4id check (40a), (40b) there; L3, L4 check them for
#    x in [0, rc].  Cell coordinates u, v, w in [0, 1] parametrize q, z, x within the domains.
# ======================================================================================

class Cert:
    def __init__(self, path):
        raw = json.load(open(path))
        self.raw = raw
        self.lam = F(raw['lambda'])
        self.lam_lo, self.lam_hi = frac_bounds(self.lam)
        self.pieces = [(F(p['lo']), F(p['hi']), [F(c) for c in p['coeffs']]) for p in raw['phi']]
        knots = [self.pieces[0][0]] + [b for _, b, _ in self.pieces]
        self.J_exact, acc = [], F(0)                     # J on each piece, in the local variable
        for a, b, co in self.pieces:
            self.J_exact.append([acc] + [co[k] / (k + 1) for k in range(len(co))])
            acc += poly_integral(co, F(0), b - a)
        self.phi = Piecewise(knots, [co for _, _, co in self.pieces])
        self.dphi = self.phi.derivative()
        self.J = Piecewise(knots, self.J_exact)
        co = raw['coefficients']
        self.p_a, self.p_c, self.beta0 = F(co['p_a']), F(co['p_c']), F(co['beta0'])
        self.canon_eps = F(co.get('canonical_eps', '0'))
        ks = [F(k) for k in co['knots']]; bs = [F(b) for b in co['beta']]; es = [F(e) for e in co['eta']]
        self.lp_knots = ks
        lin = lambda v: [[v[i], (v[i + 1] - v[i]) / (ks[i + 1] - ks[i])] for i in range(len(ks) - 1)]
        self.beta_pl, self.eta_pl = Piecewise(ks, lin(bs)), Piecewise(ks, lin(es))
        self.dbeta_pl, self.deta_pl = self.beta_pl.derivative(), self.eta_pl.derivative()
        self.p0, self.p1 = F(raw['box_range']['p0']), F(raw['box_range']['p1'])
        self.lm = {k: F(v) for k, v in raw['landmarks'].items()}
        self.rminus = self.lm['rc']

    def phi_exact(self, r):
        r = F(r)
        for a, b, co in self.pieces:
            if a <= r <= b:
                return poly_eval(co, r - a)
        raise ValueError(r)


def coefficients(cert, p, regime):
    """beta(p) and (b, a) with c(p, x) = [a (lambda - x) + b phi(x)]_+, as Duals in p."""
    nd, shape = len(p.grad), p.val.lo.shape
    if regime == 'const':          # p <= p_a: beta = beta0, c = [(1 + beta0 p) phi(x) - (lambda - x)]_+
        beta = Dual.const(I(cert.beta0), nd, shape)
        return beta, 1 + beta * p, -1
    if regime == 'lp':             # p_a <= p <= p_c: beta, eta piecewise linear on the knots
        return p.apply(cert.beta_pl, cert.dbeta_pl), p.apply(cert.eta_pl, cert.deta_pl), -1
    if regime == 'canon':          # p >= p_c: the formulas of Lemma 11(ii), beta with a slack factor
        beta = (p / p.apply_J(cert.J, cert.phi, cert.lam_hi)) * I(1 + cert.canon_eps)
        return beta, -(beta * (1 - p)), +1
    raise ValueError(regime)


def make_family(cert, name, regime, side):
    lam, rminus = I(cert.lam), I(cert.rminus)
    phi = lambda x: x.apply(cert.phi, cert.dphi, mono='dec')
    J = lambda x: x.apply_J(cert.J, cert.phi, cert.lam_hi)
    delta = lambda p, q: J(1 - p + q) - J(q)
    K = lambda p, q, z: J(z - p + q) - J(z) - J(q)

    def W(r, y):
        """W_x(y) with r = r_x: 0 below lambda, lambda - y - r phi(y) above, hull on cells
        straddling lambda (W_x is continuous)."""
        e = lam - y - r * phi(y)
        below, above = y.val.hi <= cert.lam_lo, y.val.lo >= cert.lam_hi
        sel = lambda z, lo: np.where(below, 0.0, np.where(above, z, np.minimum(z, 0.0) if lo else np.maximum(z, 0.0)))
        val = I(sel(e.val.lo, True), sel(e.val.hi, False))
        return Dual(val, [I(sel(g.lo, True), sel(g.hi, False)) for g in e.grad])

    qmax = lambda p: p if side == 'below' else Dual.const(lam, len(p.grad), p.val.lo.shape)
    corr = lambda b, a, x: (a * (lam - x) + b * phi(x)).pos()                 # c(p, x)

    def r_u(b, a, x):                                                          # r_x, u_x for x <= rc
        r = (lam - x) / phi(x)
        return r, (a * r + b).pos()

    def r_u_id(b, a, p):                                                       # r_x = 1 on [rc, lambda)
        return Dual.const(I(1.0), len(p.grad), p.val.lo.shape), (a + b).pos()

    def L1(p, u, w):                                                           # (39a)
        beta, b, a = coefficients(cert, p, regime)
        q = u * qmax(p); x = q + w * (lam - q)
        return q + beta * delta(p, q) + corr(b, a, x) - lam

    def L2(p, u, w):                                                           # (39b), p <= lambda only
        beta, b, a = coefficients(cert, p, regime)
        q = u * p; x = p + w * (lam - p)
        return q + beta * K(p, q, x) + corr(b, a, x)

    def L3(p, u, w):                                                           # (40a) / phi(x), x <= rc
        beta, b, a = coefficients(cert, p, regime)
        q = u * p; r, ux = r_u(b, a, w * rminus)
        return q + beta * delta(p, q) + W(r, q) - lam - (-phi(q)).pos() * ux

    def L3id(p, u):                                                            # (40a) / phi(x), x in [rc, lambda)
        beta, b, a = coefficients(cert, p, regime)
        q = u * p; r, ux = r_u_id(b, a, p)
        return q + beta * delta(p, q) + W(r, q) - lam - (-phi(q)).pos() * ux

    def L4(p, u, v, w):                                                        # (40b) / phi(x), x <= rc
        beta, b, a = coefficients(cert, p, regime)
        q = u * p; z = p + v * (1 - p); r, ux = r_u(b, a, w * rminus)
        return q + beta * K(p, q, z) + W(r, q) - W(r, z) - (-phi(z)).pos() * ux

    def L4id(p, u, v):                                                         # (40b) / phi(x), x in [rc, lambda)
        beta, b, a = coefficients(cert, p, regime)
        q = u * p; z = p + v * (1 - p); r, ux = r_u_id(b, a, p)
        return q + beta * K(p, q, z) + W(r, q) - W(r, z) - (-phi(z)).pos() * ux

    return {'L1': (L1, 3), 'L2': (L2, 3), 'L3': (L3, 3), 'L3id': (L3id, 2), 'L4': (L4, 4), 'L4id': (L4id, 3)}[name]


# ======================================================================================
# 6. Part 1: exact checks of every hypothesis on phi* (Lemma 8 and Lemma 11).
# ======================================================================================

def check(cond, msg):
    if not cond:
        print('FAILED:', msg); sys.exit(1)


def part1(cert):
    lam, P = cert.lam, cert.pieces
    rc, zdep, pstar = cert.lm['rc'], cert.lm['zdep'], cert.lm['pstar']
    consts = cert.raw['constants']
    m0, M = F(consts['m0']), F(consts['M'])
    p0, p1, beta0 = cert.p0, cert.p1, cert.beta0
    print('Part 1: exact checks')
    dpoly = lambda co: poly_deriv(co) if len(co) > 1 else [F(0)]
    gap = lambda a, co: [lam - a - co[0]] + [(-1 - co[1]) if len(co) > 1 else F(-1)] + [-c for c in co[2:]]  # lambda - r - phi

    # --- the shape of phi (display (26)): continuous, nonincreasing, integral 0, phi(1) = -1,
    #     phi > 0 on [0, lambda), phi <= lambda - r; equality phi = lambda - r on [rc, zdep]
    check(P[0][0] == 0 and P[-1][1] == 1, 'phi is defined on [0,1]')
    for (a, b, co), (a2, b2, co2) in zip(P, P[1:]):
        check(b == a2 and poly_eval(co, b - a) == co2[0], f'phi continuous at {float(b)}')
    for a, b, co in P:
        check(poly_nonpositive(dpoly(co), F(0), b - a), f"phi' <= 0 on [{float(a)},{float(b)}]")
    check(sum(poly_integral(co, F(0), b - a) for a, b, co in P) == 0, 'integral of phi is 0')
    check(poly_eval(P[-1][2], 1 - P[-1][0]) == -1, 'phi(1) = -1')
    for a, b, co in P:
        if a == rc and b == zdep:
            check(poly_identically_zero(gap(a, co)) and a < lam < b, 'phi = lambda - r on [rc, zdep], lambda inside')
        else:
            check(poly_nonnegative(gap(a, co), F(0), b - a), f'phi <= lambda - r on [{float(a)},{float(b)}]')
    check(cert.phi_exact(rc) > 0, 'phi(rc) > 0, hence phi > 0 on [0, lambda)')
    # --- phi(r) + r nonincreasing on [lambda, 1] (Lemma 8) and phi concave there (Lemma 11)
    prev = None
    for a, b, co in P:
        if a >= rc:
            d = dpoly(co)
            check(poly_nonpositive([d[0] + 1] + d[1:], F(0), b - a), f"phi' <= -1 on [{float(a)},{float(b)}]")
            check(poly_nonpositive(dpoly(d), F(0), b - a), f"phi'' <= 0 on [{float(a)},{float(b)}]")
            check(prev is None or prev >= poly_eval(d, F(0)), f'slope does not increase at {float(a)}')
            prev = poly_eval(d, b - a)
    # --- Lipschitz bounds (44) and the monotonicity of sigma = lambda - r - phi on [0, zdep]
    for a, b, co in P:
        d = dpoly(co)
        if b <= zdep:
            check(poly_nonnegative([d[0] + 1] + d[1:], F(0), b - a), f"phi' >= -1 on [{float(a)},{float(b)}]")
        if b <= rc:
            check(poly_nonnegative([d[0] + m0] + d[1:], F(0), b - a), f"phi' >= -m0 on [{float(a)},{float(b)}]")
        if b > p1:
            check(poly_nonnegative([d[0] + M] + d[1:], max(a, p1) - a, b - a), f"phi' >= -M on [{float(max(a, p1))},{float(b)}]")
    print('  shape of phi, monotonicity, concavity, Lipschitz bounds: ok')

    # --- Lemma 11(i): the three inequalities (43)
    phi_p0, phi_0 = cert.phi_exact(p0), cert.phi_exact(F(0))
    check(beta0 * phi_p0 >= 1, '(43) beta0 phi(p0) >= 1')
    check(p0 * (1 + beta0 * (1 + phi_0)) <= lam, '(43) p0 (1 + beta0 (1 + phi(0))) <= lambda')
    check(p0 <= cert.p_a, 'p0 <= p_a (constant regime covers (0, p_a])')
    for a, b, co in P:
        if a < lam:
            hi = min(b, lam)
            lhs = [p0 * (1 - beta0 * phi_p0) + p0 * beta0 * co[0]] + [p0 * beta0 * c for c in co[1:]]
            check(poly_nonpositive(padd(lhs, gap(a, co), -1), F(0), hi - a),
                  f'(43) p0 [1 - beta0 (phi(p0) - phi(x))] <= sigma(x) on [{float(a)},{float(hi)}]')
    print('  Lemma 11(i) hypotheses: ok')

    # --- Lemma 11(ii): the inequalities (45) as polynomials in p on [p1, 1], where J is the
    #     polynomial of the last piece; and (25) at every p in [p1, 1), q in [0, lambda], by the
    #     cell reduction of Appendix B.2
    check(p1 >= pstar, 'p1 >= pstar (J is a polynomial on [p1, 1])')
    check(lam + (1 - p1) <= zdep, 'lambda + (1 - p1) <= zdep')
    check(m0 < 1 and M >= 1, '0 < m0 < 1 <= M')
    check(cert.p_c <= p1, 'p_c <= p1 (canonical regime covers [p_c, p1])')
    a, b, co = P[-1]
    Jc = cert.J_exact[-1]
    pp, hh = [a, F(1)], [1 - a, F(-1)]                # p and 1 - p in the local variable t = p - a
    t1, ph = p1 - a, pmul(pp, hh)
    check(poly_nonpositive(padd(Jc, ph, -1), t1, 1 - a), '(45) J(p) <= p (1 - p) on [p1, 1]')
    check(poly_nonpositive(padd([m0 * x for x in ph], Jc, -1), t1, 1 - a), '(45) m0 p (1 - p) <= J(p) on [p1, 1]')
    lhs = pmul(pp, padd([F(1)], [(M + 1) * x for x in hh], -1))
    check(poly_nonnegative(padd(lhs, [(M - 1) * x for x in Jc], -1), t1, 1 - a), '(45) p (1 - (M+1)(1-p)) >= (M-1) J(p) on [p1, 1]')
    qs = [F(x) for x in consts['q_partition']]
    check(qs[0] == 0 and qs[-1] == lam, 'q-partition spans [0, lambda]')
    h0 = 1 - p1
    for qi, qj in zip(qs, qs[1:]):
        xs = min(qj + h0, lam)
        s_i = lam - xs - cert.phi_exact(xs)
        check(s_i >= 0, 'sigma >= 0')
        for q in (qi, qj):
            expr = padd(padd([(lam - q) * x for x in padd(ph, Jc, -1)], [-x / 2 for x in pmul(pp, pmul(hh, hh))]),
                        [-s_i * x for x in ph])
            check(poly_nonpositive(expr, t1, 1 - a), f'(25) near p = 1: cell [{float(qi)},{float(qj)}] at q = {float(q)}')
    print('  Lemma 11(ii) hypotheses, including (25) on [p1, 1): ok')


# ======================================================================================
# 7. Part 2: interval checks of (37), (38) for p in [p0, p1].  The p-intervals are split at
#    lambda (so that min(p, lambda) is a single expression per cell), at the regime boundaries
#    p_a, p_c, and at the knots of beta, eta.
# ======================================================================================

def part2(cert):
    opt = cert.raw['box_options']
    print('Part 2: interval checks of (37) and (38) on [p0, p1]')
    p0, p1 = frac_bounds(cert.p0)[0], frac_bounds(cert.p1)[1]
    pa_hi, (pc_lo, _) = frac_bounds(cert.p_a)[1], frac_bounds(cert.p_c)
    lam_lo, lam_hi = cert.lam_lo, cert.lam_hi

    def split(lo, hi, n):
        g = np.linspace(lo, hi, n + 1); g[0], g[-1] = lo, hi
        return [(g[i], g[i + 1]) for i in range(n)]

    kb = [frac_bounds(k) for k in cert.lp_knots]
    lp = [(kb[i][0], kb[i + 1][1]) for i in range(len(kb) - 1)]
    regimes = [('const', 'below', split(p0, pa_hi, opt['n_const'])),
               ('lp', 'below', [(a, min(b, lam_hi)) for a, b in lp if a < lam_hi]),
               ('lp', 'above', [(max(a, lam_lo), b) for a, b in lp if b > lam_lo]),
               ('canon', 'above', split(pc_lo, p1, opt['n_canon']))]
    names = {'below': ['L1', 'L2', 'L3', 'L3id', 'L4', 'L4id'], 'above': ['L1', 'L3', 'L3id', 'L4', 'L4id']}
    ok = True
    for regime, side, pcells in regimes:
        for name in names[side]:
            fun, ndim = make_family(cert, name, regime, side)
            ok &= verify(fun, product_cells(pcells, opt['nsub'], ndim), ndim, opt['min_width'],
                         opt['max_boxes'], opt['batch'], f'{name}/{regime}/{side}')
    return ok


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else str(Path(__file__).resolve().parent / 'certificate.json')
    cert = Cert(path)
    t0 = time.time()
    part1(cert)
    ok = part2(cert)
    print(f'total time {time.time() - t0:.0f}s')
    if not ok:
        print('Certificate NOT verified.'); sys.exit(1)
    print(f'Certificate verified: distortion of the g*-stable lottery is at most 1 + 2*lambda = {float(1 + 2 * cert.lam):.6f}')


if __name__ == '__main__':
    main()
