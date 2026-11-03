"""Exact elementary LI/HI/support constants for L<=p<=.65."""
from fractions import Fraction as F
import json
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.lo,self.hi=a.lo,a.hi
  else:self.lo,self.hi=F(a),F(a if b is None else b)
 def __add__(self,b):
  b=I(b);return I(self.lo+b.lo,self.hi+b.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,b):return self+-I(b)
 def __rsub__(self,b):return I(b)+-self
 def __mul__(self,b):
  b=I(b);v=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,b):
  b=I(b);assert b.lo>0;return self*I(1/b.hi,1/b.lo)
Ll,Lh=F('.562325'),F('.562330');Sl,Sh=F('.02271790'),F('.023354')
b=F('.2635');L=I(Ll,Lh);S=I(Sl,Sh)
head0=2*L*(L-F('.5'))/b+L/2-L*S*(2/(b*(1-b))-1/(1-b)**2)
phib=L/2-L*S/(1-b)**2
assert head0.lo>F('.436') and head0.hi<F('.443') and phib.hi<F('.26')
Q=lambda l,t:l*t-t*t/2
beta_max=F('.65')/(Q(Ll,F('.65'))-Sh)
assert beta_max*F('.36')<2
Pmin=Q(Ll,F('.35'))-Sh
Fpmax=Lh*Lh/2-Sl
ci_max=Lh-Ll*Pmin/Fpmax
assert ci_max<F('.1')
assert phib.lo>F('.256')
head_support=F('.443')-Ll+F('.1')*(F('.443')/phib.lo-1)
assert head_support<0
# Concave quadratic has its minimum over the p interval at an endpoint.
margin=min(p*(1+F('.436')-2*Lh)-p*p/2+Sl for p in [Ll,F('.65')])
assert margin>F('.0138')
print(json.dumps({'status':'exact intermediate LI/HI constants passed',
 'p_range':['L','.65'],'head_phi0_lower':float(head0.lo),'head_phi0_upper':float(head0.hi),
 'beta_upper':float(beta_max),'credit_upper':float(ci_max),'head_support_upper':float(head_support),
 'LI_derivative_numerator_margin':float(margin)},indent=2))
