"""Structural intermediate-mass HC certificate; no profile-distance tube.

Uses exact rational head/prefix formulas, primitive obstacles, endpoint
low slack, and a fixed selected moving inequality. The high-deviation
lower bound is obtained by ODE comparison, not by substituting an upper
bound for E into the moving inequality.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time
import numpy as np
from interval_warped_hessian import I,exp_positive

BASE=Path(__file__).resolve().parent
C=lambda s:I(F(s))
L=I(C('.562325').lo,C('.562330').hi)
b=C('.2635');c=C('.2918');contact=C('.36');on=C('.782')
Q=lambda x:L*x-x.square()/2

def rat(x,S):return L*L-L/2+L*x/2-L*S/(1-x)
def rp(x,S):return L/2-L*S/(1-x).square()
def head0(S):return 2*L*(L-C('.5'))/b+L/2-L*S*(2/(b*(1-b))-1/(1-b).square())
def head(x,S):
 f0=head0(S);s=(rp(b,S)-f0)/b
 return f0*x+s*x.square()/2

def primitive(x,S,upper):
 # All branches are genuine bounds on their closed rank domains.
 br=[(0.,float(b.hi),head),(float(b.lo),float((contact if upper else c).hi),rat),
     (float((contact if upper else c).lo),1.,lambda y,S:Q(y)-S if upper else Q(y)-S+I(np.maximum(0.,(S-Q(c)+rat(c,S)-(L-c-rp(c,S))*(y-c)).lo),np.maximum(0.,(S-Q(c)+rat(c,S)-(L-c-rp(c,S))*(y-c)).hi)))]
 shape=np.broadcast_shapes(x.lo.shape,S.lo.shape);anslo=np.full(shape,np.inf);anshi=np.full(shape,-np.inf)
 for left,right,fun in br:
  lo=np.maximum(x.lo,left);hi=np.minimum(x.hi,right);ok=lo<=hi
  safe=I(np.where(ok,lo,left),np.where(ok,hi,left));v=fun(safe,S)
  anslo=np.where(ok,np.minimum(anslo,v.lo),anslo);anshi=np.where(ok,np.maximum(anshi,v.hi),anshi)
 assert np.all(anslo<=anshi)
 if upper:
  dr=I(np.maximum(0.,(C('.348541')-x).lo),np.maximum(0.,(C('.348541')-x).hi))
  cone=Q(x)-S+C('.000000087')+C('.00024')*dr+C('.309')*dr.square()/2
  use=x.lo>=C('.313').hi
  anslo=np.where(use,np.minimum(anslo,cone.lo),anslo);anshi=np.where(use,np.minimum(anshi,cone.hi),anshi)
 return I(anslo,anshi)

def defect(x,S,upper):
 f0=head0(S);slope=(rp(b,S)-f0)/b
 def hd(y,S):return (f0-L)*y+(slope+1)*y.square()/2+S
 def rd(y,S):return L*L-L/2-L*y/2+y.square()/2+S*(1-L/(1-y))
 def last(y,S):
  if upper:return I(np.zeros(y.lo.shape))
  E0=S-Q(c)+rat(c,S);sig0=L-c-rp(c,S);lin=E0-sig0*(y-c)
  return I(np.maximum(0.,lin.lo),np.maximum(0.,lin.hi))
 br=[(0.,float(b.hi),hd),(float(b.lo),float((contact if upper else c).hi),rd),
     (float((contact if upper else c).lo),1.,last)]
 shape=np.broadcast_shapes(x.lo.shape,S.lo.shape);anslo=np.full(shape,np.inf);anshi=np.full(shape,-np.inf)
 for left,right,fun in br:
  lo=np.maximum(x.lo,left);hi=np.minimum(x.hi,right);ok=lo<=hi
  val=fun(I(np.where(ok,lo,left),np.where(ok,hi,left)),S)
  anslo=np.where(ok,np.minimum(anslo,val.lo),anslo);anshi=np.where(ok,np.maximum(anshi,val.hi),anshi)
 if upper:
  dd=I(np.maximum(0.,(C('.348541')-x).lo),np.maximum(0.,(C('.348541')-x).hi))
  con=C('.000000087')+C('.00024')*dd+C('.309')*dd.square()/2
  use=x.lo>=C('.313').hi
  anslo=np.where(use,np.minimum(anslo,con.lo),anslo);anshi=np.where(use,np.minimum(anshi,con.hi),anshi)
 return I(anslo,anshi)

def score_lower(x,S):
 # Used only below .782. The endpoint estimate gives a strong free-score floor.
 f0=head0(S);s=(rp(b,S)-f0)/b
 br=[(0.,float(b.hi),lambda y:f0+s*y),
     (float(b.lo),float(c.hi),lambda y:rp(y,S)),
     (float(c.lo),float(contact.hi),lambda y:L-y-C('.022')),
     (float(contact.lo),float(on.hi),lambda y:L-y)]
 shape=np.broadcast_shapes(x.lo.shape,S.lo.shape);lo=np.full(shape,np.inf);hi=np.full(shape,-np.inf)
 for left,right,fun in br:
  a=np.maximum(x.lo,left);bb=np.minimum(x.hi,right);ok=a<=bb
  val=fun(I(np.where(ok,a,left),np.where(ok,bb,left)))
  lo=np.where(ok,np.minimum(lo,val.lo),lo);hi=np.where(ok,np.maximum(hi,val.hi),hi)
 return I(lo,hi)

def scores(x,S):
 f0=head0(S);s=(rp(b,S)-f0)/b
 M=rp(C('.28'),S)
 br=[(0.,float(b.hi),lambda y:(f0+s*y,f0+s*y)),
     (float(b.lo),float(c.hi),lambda y:(rp(y,S),rp(y,S))),
     (float(c.lo),float(contact.hi),lambda y:(L-y-C('.022'),I(np.minimum(M.lo,(L-y).lo),np.minimum(M.hi,(L-y).hi)))),
     (float(contact.lo),float(on.hi),lambda y:(L-y,L-y)),
     (float(on.lo),1.,lambda y:(I(-1.),L-y))]
 shape=np.broadcast_shapes(x.lo.shape,S.lo.shape);lo=np.full(shape,np.inf);hi=np.full(shape,-np.inf)
 for left,right,fun in br:
  a=np.maximum(x.lo,left);bb=np.minimum(x.hi,right);ok=a<=bb
  vl,vh=fun(I(np.where(ok,a,left),np.where(ok,bb,left)))
  lo=np.where(ok,np.minimum(lo,vl.lo),lo);hi=np.where(ok,np.maximum(hi,vh.hi),hi)
 return I(lo,hi)

def params(p,S):
 beta=p/(Q(p)-S);Plo=primitive(1-p,S,False);Pup=primitive(1-p,S,True)
 ci=I(np.maximum(0.,(L-beta*Pup).lo),np.maximum(0.,(L-beta*Plo).hi))
 return beta,1+ci/rp(b,S),ci

def cut(S,z):
 r=C('.34854');a=r;bb=r
 # phi'<=-.691 on the free component; sigma(rc)<.00024,
 # rc<=.348541. Both tested roots lie strictly after every possible cap contact.
 A=L-a-C('.00024')-C('.309')*(C('.348541')-a)
 B=L-bb-C('.00024')-C('.309')*(C('.348541')-bb)
 dr=C('.348541')-r
 R=Q(r)-S+C('.000000087')+C('.00024')*dr+C('.309')*dr.square()/2;P=Q(1-r)-S;h=2*L-a;k=r+bb-L;D=h*R-k*P
 alpha=(k*A+h*B)/D;cc=(A*R+B*P)/D;m=cc-1+alpha*r
 assert np.all(D.lo>0) and np.all(alpha.lo>0) and np.all(m.lo>0)
 assert np.all((m*(C('.775')-L)-alpha*r.square()/2).hi<0)
 zc=L+alpha*r.square()/(2*m)
 s=I(np.maximum(0.,(z-zc).lo),np.maximum(0.,(z-zc).hi))
 arg=alpha*s;arg=I(np.maximum(0.,arg.lo),arg.hi)
 ee=m/alpha*(exp_positive(arg)-1)
 return I(np.maximum(0.,ee.lo),np.maximum(0.,ee.hi))

def run():
 start=time.time();sl,sh=C('.02271790'),C('.023354')
 # Continuous boxes cover every parameter; all initial endpoints enclose their exact decimals.
 active=np.array([[float(sl.lo),float(sh.hi),float(L.lo),float(C('.65').hi),0.,float(L.hi),float(on.lo),float(C('.875').hi)]])
 visited=leaves=0;worst=-np.inf;depth=0
 while len(active):
  for sweep in range(2):
   S,p,q,z=[I(active[:,j],active[:,j+1]) for j in range(0,8,2)]
   beta,eta,ci=params(p,S)
   dq=1+beta*(scores(z-p+q,S)-scores(q,S))
   inc=dq.lo>=0;dec=dq.hi<=0
   active[:,4]=np.where(inc,active[:,5],active[:,4]);active[:,5]=np.where(dec,active[:,4],active[:,5])
  S,p,q,z=[I(active[:,j],active[:,j+1]) for j in range(0,8,2)]
  beta,eta,ci=params(p,S);t=z-on
  k=eta-beta*t/2
  e=cut(S,z)
  # e >= e_min by fixed-cut ODE comparison, and E<=t e/2 by high concavity.
  value=(p-q)*(beta*(z-p)-1)+beta*(defect(z-p+q,S,True)-defect(q,S,False))-(eta-1)*(z-L)-k*I(e.lo)
  good=(value.hi<0)&(k.lo>0)
  visited+=len(active);leaves+=int(np.sum(good))
  if np.any(good):worst=max(worst,float(np.max(value.hi[good])))
  bad=active[~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'worst':worst,'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  if visited>20000000:raise RuntimeError('box budget')
  widths=bad[:,1::2]-bad[:,::2]
  # Sensitivity-scaled longest-side bisection; this choice does not enter the proof.
  weights=np.array([35.,8.,12.,15.]);which=np.argmax(widths*weights,axis=1);ids=np.arange(len(bad))
  mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid
  active=np.vstack([aa,bb]);depth+=1
 out={'status':'structural HC through .875 passed','p':['L','.65'],'z':['.782','.875'],
 'S':['.02271790','.023354'],'head':'.2635','prefix':'.2918','contact_upper':'.36',
 'low_endpoint_rank_upper':'.348541','low_endpoint_slack_upper':'.00024','free_slope_upper':'-.691',
 'leaves':leaves,'visited':visited,'HC_upper':worst,'seconds':time.time()-start,
 'hypotheses':'binary for ci>=0; global high concavity; high onset>=.782; stated low shape/primitive bounds; fixed selected cut r=a=b=.34854; fixed cap retained after Hermite join by the cap-extension lemma'}
 (BASE/'structural_intermediate_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':run()
