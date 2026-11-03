"""Exact rational lower bounds from approximate LP dual multipliers.

For Ax<=b and ell<=x<=u, any pi<=0 proves
 c*x >= pi*b + sum_j min(r_j*ell_j,r_j*u_j), r=c-A^T*pi.
The nonnegative floors include the reverse-integrated derivative majorant;
this is crucial because a positive residual at a deficit variable carries
strictly positive information even if the numerical LP used a zero bound.
No sign/zero judgement in this verification uses floating arithmetic.
The input dual proposes rational multipliers; all row data are rebuilt from
their mathematical tags. Earlier moving cuts must already be certified.
"""
from fractions import Fraction as F
from collections import defaultdict

class ExactVerifier:
 def __init__(self,lp):
  self.lp=lp;self.N=lp.N;self.L=F(str(lp.L));self.cache={}
  self.nodes=list(map(int,getattr(lp,'nodes',range(self.N+1))));self.K=len(self.nodes)
  self.indices={int(v):i for i,v in enumerate(self.nodes)}
  self.caps=[]
  for i in self.nodes:
   t=F(i,self.N);self.caps.append(self.L*t-t*t/2)
  for i in self.nodes:
   t=F(i,self.N);self.caps.append(self.L*t*t/2-t*t*t/6)
  self.caps[0]=self.caps[self.K-1]=self.caps[self.K]=F(0)
  self.floors=[];end=self.L-F(1,2);turn=2*self.L-1
  integral=lambda t:self.L*t*t/2-t*t*t/6-end*t
  for i in self.nodes:
   t=F(i,self.N);self.floors.append(max(F(0),self.L*t-t*t/2-end))
  for i in self.nodes:
   t=F(i,self.N);self.floors.append(integral(t)-integral(turn) if t>turn else F(0))
 def row(self,i):
  if i in self.cache:return self.cache[i]
  cache_key=i
  tag=self.lp.labels[i];name=tag[0];N=self.N;L=self.L;off=self.K;ix=self.indices;v=defaultdict(F);rhs=F(0)
  def add(j,x):v[j]+=x
  if name=='slope':
   j=tag[1];add(j+1,N);add(j,-N);rhs=L-F(2*j+1,2*N)
  elif name in ('moment-up','moment-low'):
   j=tag[1];h=F(1,N);t=j*h
   if name=='moment-up':
    add(off+j+1,N);add(off+j,-N);add(j,-1);rhs=(L-t)*h/2-h*h/6
   else:
    add(off+j+1,-N);add(off+j,N);add(j+1,1);rhs=(L-t)*h/2-h*h/3
  elif name in ('slope-node','moment-up-node','moment-low-node'):
   left,right=tag[1:];j=ix[left];h=F(int(right-left),N);t=F(int(left),N)
   if name=='slope-node':
    add(j+1,1/h);add(j,-1/h);rhs=L-t-h/2
   elif name=='moment-up-node':
    add(off+j+1,1/h);add(off+j,-1/h);add(j,-1);rhs=(L-t)*h/2-h*h/6
   else:
    add(off+j+1,-1/h);add(off+j,1/h);add(j+1,1);rhs=(L-t)*h/2-h*h/3
  elif name=='binary':
   i,j=tag[1:];p=F(i,N);q=F(j,N)
   add(ix[N-i+j],p);add(ix[j],-p);add(ix[i],-(L-q))
  elif name=='binary-integral':
   i,j=tag[1:];p=F(i,N);q=F(2*j+1,2*N)
   add(off+ix[N-i+j+1],p*N);add(off+ix[N-i+j],-p*N);add(off+ix[j+1],-p*N);add(off+ix[j],p*N);add(ix[i],-(L-q))
  elif name=='moving-general':
   pi,i,j,k,l,z0,z1,xf,yf=tag[1:];x=F(str(xf));y=F(str(yf));r=1-F(pi,N)
   U=F(z0+z1,2*N)-L;f=2*L-F(i+j,2*N);kap=r+F(k+l,2*N)-L
   for aa,bb,weight in [(i,j,U+kap*y),(k,l,U*x+f*y),(z0,z1,f-kap*x)]:
    mult=weight*F(N,bb-aa);add(ix[bb],mult);add(ix[aa],-mult)
  elif name=='transport':
   rs,a0,b0,z0,rt,a1,b1,z1,xf,yf=tag[1:];x=F(str(xf));y=F(str(yf));h=F(rt-rs,N)
   al=F(a1-a0,rt-rs);bl=F(b1-b0,rt-rs);zl=F(z1-z0,rt-rs)
   U=F(z0,N)-L;f=2*L-F(a0,N);k=F(rs+b0,N)-L
   terms=[(a0,a1,U+k*y,zl+(1+bl)*y),(b0,b1,U*x+f*y,zl*x-al*y),(z0,z1,f-k*x,-al-(1+bl)*x)]
   for aa,bb,c0,c1 in terms:
    slope=F(bb-aa,rt-rs)
    add(ix[bb],(c0+c1*h)/slope/h);add(ix[aa],-c0/slope/h)
    add(off+ix[bb],-c1/slope**2/h);add(off+ix[aa],c1/slope**2/h)
  else:raise ValueError(name)
  out=({j:val for j,val in v.items()if val},rhs);self.cache[cache_key]=out;return out
 def bound(self,c,multipliers,denominator=10**20):
  residual=defaultdict(F)
  for j,val in c.items():residual[j]=F(val)
  constant=F(0);used=[]
  for i,pif in enumerate(multipliers):
   if pif>=0:continue
   pi=F(round(float(pif)*denominator),denominator)
   if not pi:continue
   row,rhs=self.row(i);constant+=pi*rhs
   for j,v in row.items():residual[j]-=pi*v
   used.append((i,pi.numerator,pi.denominator))
  penalty=sum((v*(self.caps[j] if v<0 else self.floors[j]) for j,v in residual.items()),F(0))
  return constant+penalty,{'multipliers':used,'constant':[constant.numerator,constant.denominator],
    'penalty':[penalty.numerator,penalty.denominator]}
 def ratio(self,num,den,approx,out,minimum_backoff=2e-9):
  # These objectives have small rational coefficients known exactly from ranks.
  def rational_vector(v):return {i:F(str(float(x))) for i,x in enumerate(v)if x}
  nr=rational_vector(num);dr=rational_vector(den)
  backoff=minimum_backoff
  for attempt in range(12):
   x=F(int((approx-backoff)*10**10),10**10)
   c=dict(nr)
   for j,v in dr.items():c[j]=c.get(j,F(0))-x*v
   lb,proof=self.bound(c,out.ineqlin.marginals)
   if lb>=0:return x,lb,proof
   backoff*=5
  raise RuntimeError('Approximate dual could not certify a useful ratio lower bound')
