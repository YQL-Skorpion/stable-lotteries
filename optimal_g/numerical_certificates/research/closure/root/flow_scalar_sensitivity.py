"""Rigorous Taylor propagation of the transported flow's scalar sensitivity.

Uses the companion verifier's outward-rounded intervals and exact rational
reference. This certifies a first-variation enclosure, not stationarity.

The independent jet variables are S (index 0) and reference high rank t
(index 1). All jets are evaluated at S=Sstar. A linear warp z=t+(S-Sstar)v(t)
has v(t)=-(t-z0)/(z1-z0); its Jacobian multiplies BOTH flow coefficients.
"""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path
import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'global'))
from interval_warped_hessian import (
    I, J, Reference, exact_poly_range, exp_positive, flow_jets,
    numerators, outer, prepare_flow, split_cells,
)


def _jet(value, ds=0, dt=0, dss=0, dst=0, dtt=0):
    """Supply the exact derivatives on the S=Sstar slice, with interval values."""
    ds, dt, dss, dst, dtt = map(I, (ds, dt, dss, dst, dtt))
    g = I(np.zeros(3), np.zeros(3))
    h = I(np.zeros((3, 3)), np.zeros((3, 3)))
    for j, x in ((0, ds), (1, dt)):
        g.lo[j], g.hi[j] = x.lo, x.hi
    for ij, x in (((0, 0), dss), ((0, 1), dst), ((1, 0), dst), ((1, 1), dtt)):
        h.lo[ij], h.hi[ij] = x.lo, x.hi
    return J(value, g, h)


def _quotient(n, d):
    """Differentiate n=q*d; works for signed n and positive d."""
    assert np.all(d.v.lo > 0)
    value = n.v / d.v
    gradient = (n.g - value.axis() * d.g) / d.v.axis()
    hessian = (n.h - value.axis(2) * d.h
               - outer(gradient, d.g) - outer(d.g, gradient)) / d.v.axis(2)
    return J(value, gradient, hessian)


def gauge_second_range(ref, lo, hi):
    """Enclose u'' from the rational prefix or the exact polynomial u'."""
    assert not lo < ref.c < hi
    if hi <= ref.c and lo < ref.c:
        return I(I(-2 * ref.L / (1-hi)**3).lo,
                 I(-2 * ref.L / (1-lo)**3).hi)
    coeff = [F(i) * x / ref.h for i, x in enumerate(ref.du) if i]
    return I(*exact_poly_range(coeff, (lo-ref.c)/ref.h, (hi-ref.c)/ref.h))


def scalar_flow_jets(ref, cell, at=None, start=None, end=None):
    """Return jets of warped alpha and beta, including their S,t derivative.

    at=None encloses the entire cell; a Fraction in [0,1] evaluates a point.
    The third jet variable is unused. No third derivative of u is needed:
    on S=Sstar, m_tt=phi''*rank_t**2 and m_St=u''*rank_t.
    """
    left, right = cell['left'], cell['right']
    if start is None:
        start = F(str(ref.raw['controls'][0]['z']))
    if end is None:
        end = F(str(ref.raw['controls'][-1]['z']))
    rp = I((right['r']-left['r']) / cell['dz'])
    ap = I((right['a']-left['a']) / cell['dz'])
    if at is None:
        rl, rh = left['r'], right['r']
        al, ah = left['a'], right['a']
        zi = I(I(left['z']).lo, I(right['z']).hi)
        ri, ai = I(I(rl).lo, I(rh).hi), I(I(al).lo, I(ah).hi)
        rd, ad = cell['rdata'], cell['adata']
    else:
        at = F(at)
        rl = rh = left['r'] + at * (right['r']-left['r'])
        al = ah = left['a'] + at * (right['a']-left['a'])
        zi = I(left['z'] + at * cell['dz'])
        ri, ai = I(rl), I(al)
        rd, ad = ref.ranges(rl, rh), ref.ranges(al, ah)
    vp = I(-1 / (end-start))
    warp = -(zi-I(start)) / I(end-start)
    S = _jet(I(ref.S), ds=1)
    r, a = _jet(ri, dt=rp), _jet(ai, dt=ap)
    z = _jet(zi, ds=warp, dt=1, dst=vp)
    jacobian = _jet(1, ds=vp)
    R = _jet(rd['F'], ds=rd['u'], dt=rd['phi']*rp,
             dst=rd['du']*rp, dtt=rd['dphi']*rp.square())
    mr = _jet(rd['phi'], ds=rd['du'], dt=rd['dphi']*rp,
              dst=gauge_second_range(ref, rl, rh)*rp,
              dtt=rd['ddphi']*rp.square())
    ma = _jet(ad['phi'], ds=ad['du'], dt=ad['dphi']*ap,
              dst=gauge_second_range(ref, al, ah)*ap,
              dtt=ad['ddphi']*ap.square())
    D, N = numerators(I(ref.L), I(F('.135')), cell['branch'], S, r, a, R, z)
    scores = [ma, ma] if cell['branch'] == 'early' else [mr, ma, mr, ma]
    terms = [_quotient(n*m, D)*jacobian for n, m in zip(N, scores)]
    if cell['branch'] == 'early':
        return terms[0], terms[1]
    return terms[0]+terms[1], terms[2]+terms[3]


def terminal_barrier(ref, end):
    """Exact fixed-q logarithmic terminal barrier and its S derivative."""
    L, S, q, z = ref.L, ref.S, F(str(ref.raw['terminal_q'])), end
    Q = lambda t: L*t-t*t/2
    N = Q(1-z+q)-S-ref.rat_F(q)
    B = z*N/(L-q)
    Bs = z*(-1+L/(1-q))/(L-q)
    Bz = (N-z*(L-1+z-q))/(L-q)
    Zbar = F('.135')-S-B
    assert Zbar > 0
    return Zbar, (-1-Bs+Bz)/Zbar


def _terminal_flow_enclosure(ref, cell):
    """Recover a terminal enclosure from an already processed last cell."""
    aj, bj = flow_jets(ref, cell)
    a0, b0 = flow_jets(ref, cell, F(0))
    Z, h, Zcell = cell['Zleft'], I(cell['dz']), cell['Z']
    first = a0[0]*Z+b0[0]
    second = (a0[1]+a0[0].square())*Z+a0[0]*b0[0]+b0[1]
    third = ((aj[2]+3*aj[0]*aj[1]+aj[0]*aj[0]*aj[0])*Zcell
             +(2*aj[1]+aj[0].square())*bj[0]+aj[0]*bj[1]+bj[2])
    return Z+h*first+h.square()*second/2+h.square()*h*third/6


def _intersect(x, y):
    lo, hi = np.maximum(x.lo, y.lo), np.minimum(x.hi, y.hi)
    assert np.all(lo <= hi), ('disjoint rigorous enclosures', x.bounds(), y.bounds())
    return I(lo, hi)


def propagate_scalar_sensitivity(ref, cells, flow=None, include_cells=False):
    """Propagate V=Z_S through cells already processed by prepare_flow.

    V'=alpha*V+alpha_S*Z+beta_S, V(z0)=0. Each step uses the left
    first derivative and a rigorous interval enclosure of V'' throughout
    the cell. The coarse V-cell enclosure follows variation of constants.
    Accepts the optional prepare_flow result, avoiding any recomputation.
    """
    assert cells and all('Zleft' in c and 'Z' in c for c in cells)
    start, end = cells[0]['left']['z'], cells[-1]['right']['z']
    V = I(0)
    records = []
    max_vcell_width = 0.
    for cell in cells:
        aj, bj = scalar_flow_jets(ref, cell, start=start, end=end)
        a0, b0 = scalar_flow_jets(ref, cell, F(0), start, end)
        h, Zleft, Zcell = I(cell['dz']), cell['Zleft'], cell['Z']
        alpha, beta = aj.v, bj.v
        AS, BS = aj.g.take(0), bj.g.take(0)
        AT, AST, BST = aj.g.take(1), aj.h.take(0, 1), bj.h.take(0, 1)
        assert np.all(alpha.lo > 0)
        # For 0<=tau<=h: exp(integral alpha) is in [1,exp(alpha_max*h)]
        # and the inhomogeneous kernel integral is in [0,h*exp(alpha_max*h)].
        e = exp_positive(alpha*h)
        growth = I(1., e.hi)
        mass = I(0., (h*e).hi)
        force = AS*Zcell+BS
        Vcell = growth*V+mass*force
        first = a0.v*V+a0.g.take(0)*Zleft+b0.g.take(0)
        second = ((AT+alpha.square())*Vcell
                  +(2*alpha*AS+AST)*Zcell
                  +alpha*BS+AS*beta+BST)
        Vnext = V+h*first+h.square()*second/2
        Vnext = _intersect(Vnext, Vcell)
        max_vcell_width = max(max_vcell_width, float(Vcell.hi-Vcell.lo))
        if include_cells:
            records.append({'zleft': str(cell['left']['z']), 'dz': str(cell['dz']),
                            'Vleft': V.bounds(), 'Vcell': Vcell.bounds(),
                            'Vnext': Vnext.bounds(), 'Vsecond': second.bounds()})
        V = Vnext
    Zterminal = _terminal_flow_enclosure(ref, cells[-1])
    if flow is not None:
        Zterminal = _intersect(Zterminal, I(*flow['Zterminal']))
    assert Zterminal.lo > 0
    logarithmic = V/Zterminal
    Zbar, bprime = terminal_barrier(ref, end)
    residual = logarithmic-I(bprime)
    result = {'status': 'outward-rounded scalar first-variation enclosure; not stationarity',
              'cells': len(cells), 'Vterminal': V.bounds(), 'Zterminal': Zterminal.bounds(),
              'log_flow_S': logarithmic.bounds(), 'terminal_bprime': str(bprime),
              'terminal_Zbar': str(Zbar), 'scalar_residual': residual.bounds(),
              'scalar_residual_width': float((I(residual.hi)-I(residual.lo)).hi),
              'maximum_coarse_Vcell_width': max_vcell_width}
    if include_cells:
        result['steps'] = records
    return result


def adjoint_scalar_enclosure(ref, cells, flow):
    """Original transport_first_variation.py adjoint formula, independently."""
    start, end = cells[0]['left']['z'], cells[-1]['right']['z']
    answer = I(0)
    for cell in cells:
        left, right = cell['left'], cell['right']
        ri = I(I(left['r']).lo, I(right['r']).hi)
        ai = I(I(left['a']).lo, I(right['a']).hi)
        zi = I(I(left['z']).lo, I(right['z']).hi)
        S, r, a = J.var(I(ref.S), 0), J.var(ri, 1), J.var(ai, 2)
        warp = -(zi-I(start))/I(end-start)
        dwarp = I(-1/(end-start))
        z = J(zi)+(S-I(ref.S))*warp
        R = J(cell['rdata']['F'])+(S-I(ref.S))*cell['rdata']['u']
        D, N = numerators(I(ref.L), I(F('.135')), cell['branch'], S, r, a, R, z)
        weights = cell['weights']
        total = sum(weights, I(0))
        gradient = -(D.g/D.v)*total
        for n, w in zip(N, weights):
            gradient = gradient+(n.g/n.v)*w
        datasets = ([cell['adata']]*2 if cell['branch']=='early' else
                    [cell['rdata'], cell['adata'], cell['rdata'], cell['adata']])
        gs = gradient.take(0)+total*dwarp
        for data, w in zip(datasets, weights):
            gs = gs+w*data['du']/data['phi']
        answer = answer+gs*I(cell['dz'])
    _, bprime = terminal_barrier(ref, end)
    return (answer-I(bprime)).bounds()


def check_exact_symbolic_jets(ref, cells):
    """Check interval jets against independently differentiated exact formulas.

    Selected points cover the prefix, early connector, and late connector.
    SymPy differentiates the actual rational/polynomial formulas; comparisons
    use Fraction representations of the binary64 interval endpoints.
    """
    import sympy as sp
    sigma, tau = sp.symbols('sigma tau')
    rat = lambda x: sp.Rational(x.numerator, x.denominator)
    def poly(coeff, x):
        return sum((rat(c)*x**i for i, c in enumerate(coeff)), sp.Integer(0))
    def low(rank, point):
        if point < ref.c:
            primitive = rat(ref.L*ref.L-ref.L/2)+rat(ref.L)*rank/2-rat(ref.L*ref.S)/(1-rank)
            score = rat(ref.L)/2-rat(ref.L*ref.S)/(1-rank)**2
            gauge = -rat(ref.L)/(1-rank)
            dgauge = -rat(ref.L)/(1-rank)**2
        else:
            w = (rank-rat(ref.c))/rat(ref.h)
            gauge, dgauge = poly(ref.uint, w), poly(ref.du, w)
            if ref.curvature_nodes:
                piece = next(p for p in ref.pieces if p['lo'] <= point <= p['hi'])
                primitive = poly(piece['F'], rank-rat(piece['lo']))
                score = poly(piece['phi'], rank-rat(piece['lo']))
            else:
                primitive, score = poly(ref.Fint, w), poly(ref.phi, w)
        return primitive, score, gauge, dgauge
    choices = []
    for predicate in [lambda c: c['right']['r'] < ref.c,
                      lambda c: c['left']['r'] > ref.c and c['branch']=='early',
                      lambda c: c['branch']=='late']:
        eligible = [i for i, c in enumerate(cells) if predicate(c)]
        if eligible:
            choices.append(eligible[len(eligible)//2])
    checked = []
    start, end = cells[0]['left']['z'], cells[-1]['right']['z']
    for index in choices:
        cell = cells[index]
        left, right = cell['left'], cell['right']
        r0 = (left['r']+right['r'])/2
        a0 = (left['a']+right['a'])/2
        t0 = (left['z']+right['z'])/2
        r = rat(r0)+rat((right['r']-left['r'])/cell['dz'])*tau
        a = rat(a0)+rat((right['a']-left['a'])/cell['dz'])*tau
        t = rat(t0)+tau
        S = rat(ref.S)+sigma
        z = t-sigma*(t-rat(start))/rat(end-start)
        jac = 1-sigma/rat(end-start)
        Fr, pr, ur, dur = low(r, r0)
        _, pa, _, dua = low(a, a0)
        R, mr, ma = Fr+sigma*ur, pr+sigma*dur, pa+sigma*dua
        L = rat(ref.L)
        P = (1-r)*L-(1-r)**2/2-S
        U, h = z-L, 2*L-a
        K = (z-r)*L-(z-r)**2/2-rat(F('.135'))
        k = r+a-L if cell['branch']=='early' else 2*r-L
        D = h*R-k*P
        if cell['branch']=='early':
            expressions = [(L+r)*ma*jac/D,
                           (U*(R+P)+(L+r)*K)*ma*jac/D]
        else:
            expressions = [(h*mr+k*ma)*jac/D,
                           ((U*P+h*K)*mr+(U*R+k*K)*ma)*jac/D]
        actual = scalar_flow_jets(ref, cell, F(1,2), start, end)
        for name, expr, jet in zip(('alpha','beta'), expressions, actual):
            val = expr.subs(sigma, 0)
            ds = sp.diff(expr, sigma).subs(sigma, 0)
            tests = [('value', val, jet.v), ('S', ds, jet.g.take(0)),
                     ('time', sp.diff(val, tau), jet.g.take(1)),
                     ('S_time', sp.diff(ds, tau), jet.h.take(0,1))]
            for derivative, expression, box in tests:
                exact = expression.subs(tau, 0)
                exact = F(int(exact.p), int(exact.q))
                assert F(float(box.lo)) <= exact <= F(float(box.hi)), (index,name,derivative,box.bounds())
                checked.append({'cell': index, 'coefficient': name, 'derivative': derivative})
    return {'method': 'exact symbolic differentiation and rational containment',
            'passed': len(checked), 'selected_cells': choices}


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--reference', default='research/closure/root/warped_cubic_ordered_reference_242.json')
    p.add_argument('--subdivisions', type=int, default=1)
    p.add_argument('--output')
    p.add_argument('--adjoint-check', action='store_true')
    p.add_argument('--jet-check', action='store_true')
    args = p.parse_args()
    ref = Reference(args.reference)
    cells = split_cells(ref, args.subdivisions)
    flow = prepare_flow(ref, cells)
    result = propagate_scalar_sensitivity(ref, cells, flow)
    result.update(reference=args.reference, subdivisions=args.subdivisions)
    if args.jet_check:
        result['exact_symbolic_jet_check'] = check_exact_symbolic_jets(ref, cells)
    if args.adjoint_check:
        result['adjoint_scalar_check'] = adjoint_scalar_enclosure(ref, cells, flow)
        assert max(result['scalar_residual'][0], result['adjoint_scalar_check'][0]) <= min(result['scalar_residual'][1], result['adjoint_scalar_check'][1])
    if args.output:
        Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
