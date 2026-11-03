"""Exact ancillary constants for the current compact threshold definition.

This checks only the constants identified below, not the upper theorem.
All comparisons use Fraction arithmetic; decimals in output are descriptive.
"""
from fractions import Fraction as F
from pathlib import Path
import json


class I:
    def __init__(self, a, b=None):
        if isinstance(a, I):
            self.lo, self.hi = a.lo, a.hi
        else:
            self.lo, self.hi = F(a), F(a if b is None else b)
    def __add__(self, y):
        y = I(y)
        return I(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.hi, -self.lo)
    def __sub__(self, y):
        return self+-I(y)
    def __rsub__(self, y):
        return I(y)+-self
    def __mul__(self, y):
        y = I(y)
        v = [a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return I(min(v),max(v))
    __rmul__ = __mul__
    def __truediv__(self, y):
        y = I(y)
        assert y.lo > 0
        return self*I(1/y.hi,1/y.lo)


Ll,Lh=F('.562325'),F('.562330')
Sl=F(28711863873,1306700000000)
Sh=F('.0266503148804352')
ell,d=F('.28'),F('.385')
Q=lambda L,t:L*t-t*t/2
B=lambda L,S,t:L*(Q(L,1-t)-S)/(1-t)
L,S=I(Ll,Lh),I(Sl,Sh)

# Opposite binary is redundant on the compact low class:
# F(r)>=Q(r)-S follows from the endpoint area and score ceiling.
opp=F(1)
for i in range(2048):
    r=I(F('.25')+F('.11')*i/2048,
        F('.25')+F('.11')*(i+1)/2048)
    gap=L*(Q(L,r)-S)-r*(Q(L,1-r)-S)
    opp=min(opp,gap.lo)
assert opp>F('.014')

# The chosen lower scalar endpoint is strictly inactive for every low
# feasible profile. This follows from the cap and ceiling at one rank.
r=F('.306885')
Sb=((1-r)*Q(I(Lh),r)-I(Lh)*Q(I(Lh),1-r))/(1-r-Lh)
assert Sb.lo>Sl
assert (L*L-2*L*(1-r)+F('.5')-r*r).hi<0
assert Lh/2-F('.2854')+Lh*F('.023354')/(1-F('.2854'))**2<F('.022')
# Direct truncated-class parameter transfer preserves the entire cap.
# Linear and quadratic delta coefficients are bounded separately.
transfer_cap=2*Ll-F('.5')+F('.25')/2-(Sh+F('.2012')*Lh)/(1-d)-F('.1788')-F('.005')
assert transfer_cap>F('.338')
assert 1-F('.2012')/(1-d)>0

# At every high rank the one selected binary test q=.27 lies strictly
# above the root budget. Thus a zero-valued critical objective cannot
# have a root-budget terminal test as its sole active component.
q=F('.27');budget=F(1);beta_abs=F(0)
for i in range(1024):
    z=I(F('.775')+F('.1')*i/1024,
        F('.775')+F('.1')*(i+1)/1024)
    barrier=z*(Q(L,1-z+q)-S-B(L,S,q))/(L-q)
    budget=min(budget,(barrier-Q(L,z)+Q(L,1)).lo)
for i in range(1024):
    q=I(F('.26')+F('.02')*i/1024,
        F('.26')+F('.02')*(i+1)/1024)
    beta_abs=max(beta_abs,(F('.875')*(1-q-L)/((L-q)*(1-q))).hi)
assert budget>F('.019')
assert beta_abs<F('.765')
assert (1-F('.765'))/(1-Ll/(1-ell))>F('1.073')

# Updated coarse two-rank regularity constants. No use of the obsolete
# root-max .35, D>.059, alpha<4, or 43-Lipschitz constants occurs here.
Pmin=Q(Ll,F('.75'))-F('.0267')
assert (F('.775')-Lh)*Pmin>F('.024')
assert F('.313')*F('.135')+F('.84')*F('.111315')<F('.14')
assert F('.14')/F('.0519')<F('2.7')
assert F('.024')/F('.116')>F('.2')
assert F('.84')/Pmin<F('7.4')
# The artificially transported third score need not remain on an active
# cap. Use |alpha|<=max(h,A)/P<7.4, from alpha=(Ch-A)/P and 0<=C<=1.
geom=F('7.4')*(F('.313')+F('.74')*F('.188')
               +F('.148')*F('.116')/F('.024'))+1
lip=F('2.7')*(geom+1)/F('.2')
assert geom<F('9.7') and lip<F('200')

out={
    'status':'exact current compact-class ancillary constants passed',
    'low_interval':['.28','.385'],
    'root_interval':['.285','.38'],
    'layers':['.25','.36'],
    'opposite_binary_margin_lower':float(opp),
    'strict_lower_scalar_margin':float(Sb.lo-Sl),
    'binary_above_root_budget_margin':float(budget),
    'binary_scalar_derivative_absolute_upper':float(beta_abs),
    'area_multiplier_upper':'-1.073',
    'coarse_two_rank_Lipschitz_upper':float(lip),
    'safe_stated_Lipschitz_constant':200,
}
Path(__file__).with_name('master_compact_constants_certificate.json').write_text(
    json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
