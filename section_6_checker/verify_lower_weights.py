"""Exact check of a weights-only lower-bound certificate (lower_certificate.json).

The certificate asserts that no continuous nonincreasing phi with integral zero satisfies
conditions (24) and (25) of the paper at the stated lambda.  It consists of nonnegative
multipliers for the rows of the discretized system below, multipliers for the two equalities
J(0) = J(1) = 0, and multipliers for the analytic box bounds.  This script rebuilds every row
in exact rational arithmetic and checks the Farkas identity with a rigorous allowance for the
rounding of the multipliers.

Rows (grid r_i = i/n, unknowns phi_i for i < n and J_i for i <= n):
  monotone     phi_i - phi_{i+1} >= 0
  sandwich     J_{i+1} - J_i - h phi_{i+1} >= 0 (i <= n-2),   h phi_i - (J_{i+1} - J_i) >= 0
  (24)         lam - i/n - phi_i >= 0
  (25)         (lam - q) J_a - p (J_{n-a+b} - J_b) >= 0,   p = a/n, q = b/n, b <= min(a, lam n), b in steps of q_step
  box          phi_i >= -lam^2/(2(1 - i/n)),  phi_i <= lam,  0 <= J_i <= lam^2/2   (valid for every phi in A_lambda)
Usage:  python3 verify_lower_weights.py lower_certificate.json
"""
import sys, json
from fractions import Fraction as F
from pathlib import Path


def main(path):
    cert = json.load(open(path))
    n, qs, lam = cert['n'], cert['q_step'], F(cert['lambda'])
    lam_box = F(cert['lambda_box'])
    assert lam <= lam_box
    assert not cert.get('use29'), 'this verifier handles the (24)+(25) certificate'
    nv = 2 * n + 1
    phi = lambda i: i
    J = lambda i: n + i
    h = F(1, n)
    rows = []          # (dict col->coef, rhs): row . v >= rhs
    for i in range(n - 1):
        rows.append(({phi(i): F(1), phi(i + 1): F(-1)}, F(0)))
    for i in range(n - 1):
        rows.append(({J(i + 1): F(1), J(i): F(-1), phi(i + 1): -h}, F(0)))
    for i in range(n):
        rows.append(({phi(i): h, J(i + 1): F(-1), J(i): F(1)}, F(0)))
    for i in range(n):
        rows.append(({phi(i): F(-1)}, F(i, n) - lam))
    bmax = int((lam_box * n).__floor__())
    for a in range(1, n):
        p = F(a, n)
        for b in range(0, min(a, bmax) + 1, qs):
            q = F(b, n)
            d = {}
            d[J(a)] = d.get(J(a), F(0)) + (lam - q)
            d[J(n - a + b)] = d.get(J(n - a + b), F(0)) - p
            d[J(b)] = d.get(J(b), F(0)) + p
            rows.append((d, F(0)))
    m = len(rows)
    fin = cert['final']
    y = {int(i): F(v) for i, v in fin['y']}
    assert all(v >= 0 for v in y.values()), 'negative row multiplier'
    assert max(y) < m, 'multiplier index out of range'
    mu = [F(v) for v in fin['mu']]
    lo_m = {int(i): F(v) for i, v in fin['lo']}     # multipliers of  v_i >= lb_i   (>= 0)
    up_m = {int(i): F(v) for i, v in fin['up']}     # multipliers of  v_i <= ub_i   (<= 0 as reported; use -)
    # analytic box
    lb = {}; ub = {}
    for i in range(n):
        lb[phi(i)] = -lam_box * lam_box / (2 * (1 - F(i, n))); ub[phi(i)] = lam_box
    for i in range(n + 1):
        lb[J(i)] = F(0); ub[J(i)] = lam_box * lam_box / 2
    # combination:  sum_r y_r (row_r . v - rhs_r) + mu_0 J_0 + mu_1 J_n + sum lo_i (v_i - lb_i) + sum (-up_i)(ub_i - v_i) >= 0
    # for every feasible v;  collect coefficients c of v and the constant s:  c . v - s >= 0.
    c = {}; s = F(0)
    for r, yr in y.items():
        d, rhs = rows[r]
        for j, a in d.items():
            c[j] = c.get(j, F(0)) + yr * a
        s += yr * rhs
    # equality multipliers: the identity is A^T y + lo - up = A_eq^T mu, and A_eq v = 0 on the feasible set,
    # so subtracting mu here leaves c . v unchanged and makes the residual c small
    c[J(0)] = c.get(J(0), F(0)) - mu[0]; c[J(n)] = c.get(J(n), F(0)) - mu[1]
    for i, v in lo_m.items():
        assert v >= 0, 'negative lower-bound multiplier'
        c[i] = c.get(i, F(0)) + v; s += v * lb[i]
    for i, v in up_m.items():
        assert v <= 0, 'positive upper-bound multiplier'
        c[i] = c.get(i, F(0)) + v; s += v * ub[i]
    # Every feasible v satisfies  c . v >= s.  Contradiction if max over the box of c . v < s.
    cmax = sum((a * ub[j] if a > 0 else a * lb[j]) for j, a in c.items())
    print(f'n={n} q_step={qs} lambda={float(lam):.6f}: rows={m}, nonzero multipliers={len(y)}')
    print(f'  residual coefficients: max |c_j| = {float(max(abs(a) for a in c.values())):.2e}')
    print(f'  s - max_box(c.v) = {float(s - cmax):+.3e}')
    if s > cmax:
        print(f'Lower certificate verified: every activation function has distortion at least 1 + 2*lambda = {float(1 + 2 * lam):.6f}')
        return True
    print('NOT verified'); return False


if __name__ == '__main__':
    ok = main(sys.argv[1] if len(sys.argv) > 1 else str(Path(__file__).resolve().parent / 'lower_certificate.json'))
    sys.exit(0 if ok else 1)
