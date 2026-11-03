"""Outward interval LI proof for all p>=.88 and long low secants.

Uses only the matched affine head, rational primitive cap, low ceiling
slack <=.022, central contact before .36, and -6.7<=phi'<=-2 on
[.88,1]. No numerical-reference proximity is assumed.
"""
import json,time
import numpy as np
from fractions import Fraction as F
from pathlib import Path
from interval_warped_hessian import I
from certify_structural_intermediate import L,C,b,c,head0,head,rat,rp
S=I(C('.02271790').lo,C('.023354').hi)
f0=head0(S);sl=(rp(b,S)-f0)/b

def lower_score(a):
 ans=np.full(a.lo.shape,np.inf)
 for left,right,kind in [(0.,float(b.hi),0),(float(b.lo),float(c.hi),1),(float(c.lo),float(C('.36').hi),2)]:
  hit=(a.hi>=left)&(a.lo<=right);x=I(np.maximum(left,np.minimum(right,a.lo)),np.maximum(left,np.minimum(right,a.hi)))
  v=f0+sl*x if kind==0 else rp(x,S) if kind==1 else L-x-C('.022')
  ans=np.where(hit,np.minimum(ans,v.lo),ans)
 return I(ans)

def average_upper(q,h):
 # If q+h is in the affine head, the average is exact and has no small-h division.
 hithead=(q+h).lo<=b.hi;vh=f0+sl*(q+h/2)
 ans=np.where(hithead,vh.hi,-np.inf)
 hitrat=(q+h).hi>=b.lo
 # q<=.18 implies h>=b-q>=.0835 on the non-head branch.
 hlo=np.maximum(h.lo,(b-q).lo);safe=I(np.where(hitrat,hlo,.1),np.where(hitrat,h.hi,.1))
 v=(rat(q+safe,S)-head(q,S))/safe
 return I(np.maximum(ans,np.where(hitrat,v.hi,-np.inf)))

def run():
 start=time.time();active=np.array([[0.,float(C('.12').hi),float(C('.18').lo),float(C('.36').hi),0.,float(C('.18').hi)]])
 visited=leaves=0;worst=-np.inf;depth=0
 while len(active):
  # Physical domain a-q>=.18. These projections retain every admissible point.
  active=active[(I(active[:,3])-I(active[:,4])).hi>=C('.18').lo]
  active[:,2]=np.maximum(active[:,2],(I(active[:,4])+C('.18')).lo)
  active[:,5]=np.minimum(active[:,5],(I(active[:,3])-C('.18')).hi)
  h,a,q=[I(active[:,j],active[:,j+1]) for j in range(0,6,2)]
  t=(1-h)/(1-C('3.35')*h)
  av=average_upper(q,h);lo=lower_score(a)
  # Actual average-phi(a)>=0 because h<=.12<a-q.
  dd=I(np.maximum(0.,(av-lo).lo),np.maximum(0.,(av-lo).hi))
  value=q-a+t*dd;visited+=len(active);good=value.hi<0;leaves+=int(np.sum(good))
  if np.any(good):worst=max(worst,float(np.max(value.hi[good])))
  bad=active[~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  assert visited<1000000
  widths=bad[:,1::2]-bad[:,::2];which=np.argmax(widths*np.array([5.,3.,3.]),axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'structural long-secant LI passed for every p>=.88','h':['0','.12'],'a_minus_q_lower':'.18','a_upper':'.36','visited':visited,'leaves':leaves,'LI_upper':worst,'seconds':time.time()-start,
 'combination':'short secants use the existing rearrangement lemma; roots a>=.36 have zero credit because beta*h>=1, and require the binary inequality'}
 Path(__file__).with_name('structural_long_credit_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':run()
