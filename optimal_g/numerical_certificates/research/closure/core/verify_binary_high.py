"""Exact rational bounds for the large-mass binary barrier up to .875.
All primitive inputs are ranges proved for the selected critical optimizer.
This script does not certify the opposite binary orientation or tail completion.
"""
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path
class I:
 def __init__(self,x,y=None):
  if isinstance(x,I):self.lo,self.hi=x.lo,x.hi
  else:self.lo,self.hi=F(x),F(x if y is None else y)
 def __add__(self,y):
  if isinstance(y,J):return NotImplemented
  y=I(y);return I(self.lo+y.lo,self.hi+y.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,y):
  if isinstance(y,J):return NotImplemented
  return self+-I(y)
 def __rsub__(self,y):return I(y)+-self
 def __mul__(self,y):
  if isinstance(y,J):return NotImplemented
  y=I(y);v=[a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,y):
  if isinstance(y,J):return NotImplemented
  y=I(y);assert y.lo*y.hi>0
  return self*I(1/y.hi,1/y.lo)
 def __rtruediv__(self,y):return I(y)/self
 def __pow__(self,n):
  if n==2:
   return I(0 if self.lo<=0<=self.hi else min(self.lo*self.lo,self.hi*self.hi),max(self.lo*self.lo,self.hi*self.hi))
  a=I(1)
  for _ in range(n):a=a*self
  return a
 def sqrt(self):
  assert self.lo>=0
  den=10**30
  a=isqrt(self.lo.numerator*den*den//self.lo.denominator)
  b=isqrt(self.hi.numerator*den*den//self.hi.denominator)+1
  assert F(a*a,den*den)<=self.lo<=self.hi<=F(b*b,den*den)
  return I(F(a,den),F(b,den))
 def pos(self):return I(max(self.lo,0),max(self.hi,0))

class J:
 def __init__(self,v,g=None):self.v=I(v);self.g=[I(0)]*5 if g is None else g
 @staticmethod
 def var(v,j):
  x=J(v);x.g=x.g.copy();x.g[j]=I(1);return x
 def __add__(self,o):
  o=o if isinstance(o,J) else J(o);return J(self.v+o.v,[a+b for a,b in zip(self.g,o.g)])
 __radd__=__add__
 def __neg__(self):return J(-self.v,[-a for a in self.g])
 def __sub__(self,o):return self+-o if isinstance(o,J) else self+-I(o)
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,J) else J(o);return J(self.v*o.v,[a*o.v+self.v*b for a,b in zip(self.g,o.g)])
 __rmul__=__mul__
 def reciprocal(self):return J(1/self.v,[-a/(self.v**2) for a in self.g])
 def __truediv__(self,o):return self*(o if isinstance(o,J) else J(o)).reciprocal()
 def __rtruediv__(self,o):return self.reciprocal()*o
 def __pow__(self,n):
  if n==0:return J(1)
  return J(self.v**n,[n*(self.v**(n-1))*a for a in self.g])
 def sqrt(self):
  v=self.v.sqrt();return J(v,[a/(2*v) for a in self.g])
 def pos(self):
  fac=I(0) if self.v.hi<=0 else I(1) if self.v.lo>=0 else I(0,1)
  return J(self.v.pos(),[fac*a for a in self.g])

def vals(L,S):
 b=I('.2635')
 Q=lambda t:L*t-t*t/2
 B=lambda t:L*L-L/2+L*t/2-L*S/(1-t)
 ph=lambda t:L/2-L*S/(1-t)**2
 A=2*B(b)/b-ph(b);be=(A-ph(b))/b
 fh=lambda t:A*t-be*t*t/2
 sigma=lambda t:L-t-(A-be*t)
 H2=lambda t:2*(L-t)*sigma(t)-2*(S-Q(t)+fh(t))
 return b,Q,B,ph,A,be,fh,sigma,H2

BOX=[I('.562325','.562330'),I('.02271790','.023354')]
records={}
def certify(name,fn,domain,target='0',maxdepth=35):
 stack=[(domain,0)];floor=None;n=0
 while stack:
  box,d=stack.pop()
  try:res=fn(*box);domain_ok=True
  except (AssertionError,ZeroDivisionError):res=I(-1,1);domain_ok=False
  if domain_ok and res.lo<=F(target):
   jet=fn(*[J.var(x,j) for j,x in enumerate(box)])
   mid=[I((x.lo+x.hi)/2) for x in box];center=fn(*mid)
   mean=center
   for j,x in enumerate(box):mean=mean+jet.g[j]*(x-mid[j])
   res=I(max(res.lo,mean.lo),min(res.hi,mean.hi))
  ok=res.lo>F(target)
  if ok:
   floor=res.lo if floor is None else min(floor,res.lo);n+=1;continue
  if d>=maxdepth:raise RuntimeError((name,'failed',[(float(x.lo),float(x.hi)) for x in box],float(res.lo),float(res.hi)))
  widths=[(x.hi-x.lo)*([10,10,1][j]) for j,x in enumerate(box)]
  j=max(range(len(box)),key=lambda j:widths[j]);x=box[j];mid=(x.lo+x.hi)/2
  for lo,hi in [(x.lo,mid),(mid,x.hi)]:
   child=box.copy();child[j]=I(lo,hi);stack.append((child,d+1))
 records[name]={'leaves':n,'strict_lower':str(floor),'decimal_lower':float(floor)}
 print(name,n,float(floor),flush=True)

certify('head slope below .691',lambda L,S:I('.691')-vals(L,S)[5],BOX)
certify('head slope above .67',lambda L,S:vals(L,S)[5]-I('.67'),BOX)
certify('rational slope above head slope',lambda L,S:vals(L,S)[5]-2*L*S/(1-I('.38'))**3,BOX)
# For all z in [.775,.875], the endpoint at q=b is central or above,
# hence N decreases beyond b, and q=.28 gives a strictly negative N.
def minusN28(L,S,z):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S);q=I('.28');h=1-z
 si=L-q-ph(q);return (h*h-(2*(L-q)*si-2*(S-Q(q)+B(q))))/2
certify('N(.28,h) negative',minusN28,BOX+[I('.775','.875')])
# Global-head lemma for z<=.85, using the known central endpoint d.
def at_d(L,S,z,which):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S);d=I('.35945');h=1-z;q=d-h
 delta=Q(d)-S-fh(q)
 if which=='N':return (L-q)*(L-d-A+be*q)+delta
 return delta/(L-q)-fh(h)/L
certify('N at central endpoint positive',lambda L,S,z:at_d(L,S,z,'N'),BOX+[I('.775','.85')])
certify('q0 dominated by central test',lambda L,S,z:at_d(L,S,z,'J'),BOX+[I('.775','.85')])
# At z=.85 the head derivative is positive at both endpoints; the
# head has one hump in N, hence no head maximizer for later z.
certify('head N0 at h=.15',lambda L,S:vals(L,S)[4]-vals(L,S)[5]*(L+I('.075')),BOX)
def Nb(L,S):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 return (H2(b)-I('.15')**2)/2
certify('head Nb at h=.15',Nb,BOX)
# The head-to-rational maximizing rank switch lies in [.849,.85].
certify('head switch before .85',lambda L,S:2*Nb(L,S),BOX)
certify('head switch after .849',lambda L,S:I('.151')**2-(2*Nb(L,S)+I('.15')**2),BOX)

certify('large-mass upper primitive below p(1-p)',lambda L,S,p:p*(1-p)-(L*p-p*p/2-S),BOX+[I('.775','.875')])

# Central-endpoint stationary head rank. The quadratic equation gives
# q=L-sqrt((h^2-D)/(1-beta)), D=2L(L-A)-2S-(1-beta)L^2.
def barrier(L,S,z):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S);h=1-z
 D=2*L*(L-A)-2*S-(1-be)*L*L
 q=L-((h*h-D)/(1-be)).sqrt()
 bv=z*(h-sg(q));bd=1-2*z-sg(q)+z*h/(L-q)
 return q,bv,bd

def earlymargin(L,S,z):
 q,bv,bd=barrier(L,S,z);Q=vals(L,S)[1]
 return Q(z)-S-bv-I('.798')*((z-I('.782')).pos()**2)
certify('early high ceiling deficit margin',earlymargin,BOX+[I('.775','.807')])
# For z after .807 and before head switch, choose selected rational
# roots a=b=.2918 and selected layer r=.29. The fixed cap dominates
# the optimal derivative from above, so its negative residual permits
# backward comparison from the selected q=b terminal barrier.
def backward_margin(L,S,z):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 q,bv,bd=barrier(L,S,z)
 r=I('.29');a=I('.2918');R=B(r);P=Q(1-r)-S;h=2*L-a;k=r+a-L
 D=h*R-k*P;C=ph(a)*(R+P)/D;al=ph(a)*(L+r)/D
 return bd-(-C*(z-L)+al*(bv-Q(z-r)+S))
certify('backward head comparison',backward_margin,BOX+[I('.807','.85')])
# The exponential bound used in the high deficit comparison is exact:
# exp(4.53*.025)<1.13 via its positive Taylor series and geometric tail.
x=F('4.53')*F('.025');term=F(1);sm=term
for n in range(1,16):term*=x/n;sm+=term
rem=term*x/16/(1-x/17)
assert sm+rem<F('1.13')
assert F('.798')>F('1.4108')*F('1.13')/2
records['exponential']={'upper':str(sm+rem),'coefficient':'.798'}
out=Path(__file__).with_name('binary_high_certificate.json');out.write_text(json.dumps(records,indent=2)+'\n')
print('All exact bounds passed:',out)
