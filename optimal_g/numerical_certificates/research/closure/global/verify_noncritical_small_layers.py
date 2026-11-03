"""Exact broad-neighborhood upper bounds for split A and small layers.

Only Fraction arithmetic is used. This verifies constants in the adjoining
note, not the remaining middle/large layer constraints.
"""
from fractions import Fraction as F
import json

L0, L1 = F('.562325'), F('.562330')
S0, S1 = F('.0219728'), F('.0266504')
p0 = F('.04')
head_min, head_max, low_endpoint_max = F('.41'), F('.45'), F('.26')
tail_slope = F(8)

# The p in [1-L,L] split-A derivative numerator decreases with p and L.
assert 1 + head_min - 2*L0 - (1-L1) < 0
assert 1 + head_min - 5*L0 < 0
split_A_margin = (1+head_min)*L1-F(5,2)*L1*L1+S0
assert split_A_margin > F('.024')

# R/p >= rho, P/p >= tau, P/p <= 1; eta=1+beta*p.
rho = head_min-p0/2
tau = 1-tail_slope*p0/2
vmax = (L1+p0)/(rho+tau)
cmin = (L0*rho-p0)/(1+rho)
assert vmax < F('.49')
assert cmin > 0

# Affine head endpoints and all later low scores obey this same support cap.
# a+eta*phi(a) <= L+vmax*.26 for eta<=1+vmax.
assert (1+vmax)*head_max <= L0+vmax*low_endpoint_max
assert F('.28')+low_endpoint_max <= L0
support_margin = cmin-vmax*low_endpoint_max
assert support_margin > F('.0016')

# An independent, elementary rational interval check of the head neighborhood
# for the area/score-matched affine extension of B_S at b0 in [.26,.28].
class I:
    def __init__(self, lo, hi=None):
        self.lo=F(lo); self.hi=F(lo if hi is None else hi)
    def __add__(self,o):
        o=o if isinstance(o,I) else I(o)
        return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-o if isinstance(o,I) else self+(-F(o))
    def __rsub__(self,o):return -self+o
    def __mul__(self,o):
        o=o if isinstance(o,I) else I(o)
        v=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=o if isinstance(o,I) else I(o)
        assert o.lo>0
        return self*I(1/o.hi,1/o.lo)

head_bounds=[F(1),F(0)]
endpoint_bounds=[F(1),F(0)]
for j in range(2000):
    b=I(F('.26')+F('.02')*j/2000,F('.26')+F('.02')*(j+1)/2000)
    L,S=I(L0,L1),I(S0,S1)
    one_b=1-b
    score=L/2-L*S/(one_b*one_b)
    # Collect S first to avoid throwing away its exact shared dependence.
    head=2*L*(L-F('.5'))/b+L/2+L*S*(3*b-2)/(b*one_b*one_b)
    head_bounds=[min(head_bounds[0],head.lo),max(head_bounds[1],head.hi)]
    endpoint_bounds=[min(endpoint_bounds[0],score.lo),max(endpoint_bounds[1],score.hi)]
assert head_bounds[0]>head_min and head_bounds[1]<head_max
assert endpoint_bounds[1]<low_endpoint_max

print(json.dumps({
    'status':'exact small-layer and split-A bounds passed',
    'small_layer_range':[0,float(p0)],
    'eta_minus_one_upper':float(vmax),
    'credit_c_lower':float(cmin),
    'small_layer_support_slack_lower':float(support_margin),
    'split_A_derivative_numerator_margin':float(split_A_margin),
    'matched_affine_head_phi0_enclosure':list(map(float,head_bounds)),
    'matched_affine_head_endpoint_enclosure':list(map(float,endpoint_bounds)),
},indent=2))
