"""Structural binary inequalities for p>=.98 from a low-slack floor.

The coupled Hermite deficit ratio bound is independently certified in
core/verify_tail_deficit_ratio.py. This script uses no sampled profile.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time
import numpy as np
from interval_warped_hessian import I
C=lambda s:I(F(s))
L=I(C('.562325').lo,C('.562330').hi)
Sl,Sh=C('.02271790'),C('.023354');k=C('.309');D=C('.35945');h=C('.02')

def floor_gap(S,c,q):
 s=L/2-c+L*S/(1-c).square()
 E=L*L-L/2-L*c/2+c.square()/2+S*(1-L/(1-c))
 feasible1=E-s.square()/(2*k)
 assert np.all(s.lo>0)
 d0=c+E/s+s/(2*k)
 feasible=(feasible1.hi>=0)&(d0.lo<=D.hi)
 # Integrate the known rational prefix first, then the universal floor.
 diff=c-q
 plen=I(np.minimum(h.lo,np.maximum(0.,diff.lo)),np.minimum(h.hi,np.maximum(0.,diff.hi)))
 end=I(np.minimum((q+h).lo,c.lo),np.minimum((q+h).hi,c.hi))
 send=L/2-end+L*S/(1-end).square()
 start=I(np.maximum(q.lo,c.lo),np.maximum(q.hi,c.hi))
 ht=h-plen;ht=I(np.maximum(0.,ht.lo),np.maximum(0.,ht.hi))
 dd=d0-start;d=I(np.maximum(0.,dd.lo),np.maximum(0.,dd.hi))
 # J(d,t)=integral_0^t (d-u)_+ du is increasing in both arguments.
 dl,dh,tl,th=I(d.lo),I(d.hi),I(ht.lo),I(ht.hi)
 jl=np.where(d.lo<=ht.lo,(dl.square()/2).lo,(tl*dl-tl.square()/2).lo)
 jh=np.where(d.hi<=ht.hi,(dh.square()/2).hi,(th*dh-th.square()/2).hi)
 J=I(np.maximum(0.,jl),np.maximum(0.,jh))
 integral=plen*send+s/(s/k+D-start)*J
 kap=C('2.122')+C('140')*(S-Sl)
 gap=integral/h.square()-kap*(L-q)+C('.5')
 return gap,feasible

def run():
 start=time.time();active=np.array([[float(Sl.lo),float(Sh.hi),float(C('.2918').lo),float(C('.305').hi),float(C('.25').lo),float(C('.337').hi)]])
 visited=leaves=discarded=0;minimum=np.inf;depth=0
 while len(active):
  S,c,q=[I(active[:,j],active[:,j+1]) for j in range(0,6,2)]
  gap,feasible=floor_gap(S,c,q);visited+=len(active);discarded+=int(np.sum(~feasible))
  good=(gap.lo>0)&feasible;leaves+=int(np.sum(good))
  if np.any(good):minimum=min(minimum,float(np.min(gap.lo[good])))
  bad=active[feasible&~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'discarded':discarded,'lower':minimum,'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  assert visited<10000000,'box budget exceeded'
  widths=bad[:,1::2]-bad[:,::2];which=np.argmax(widths*np.array([100.,3.,1.]),axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 # q<=.25: sigma is nonincreasing and q+h<=.27, in the known prefix.
 sigma27=C('.562325')/2-C('.27')+C('.562325')*Sl/(1-C('.27')).square()
 kapmax=C('2.122')+C('140')*(Sh-Sl)
 early=sigma27/h-kapmax*L+C('.5')
 late=C('.5')-kapmax*(L-C('.337'))
 assert early.lo>0 and late.lo>0
 out={'status':'structural near-one binary passed for p>=.98','q_checked':['.25','.337'],
 'last_cap':['.2918','.305'],'contact_upper':'.35945','slope_gap':'.309',
 'kappa_bound':'2.122+140*(S-.02271790)','visited':visited,'leaves':leaves,'infeasible_boxes_discarded':discarded,
 'normalized_binary_margin_lower':minimum,'q_below_025_margin':float(early.lo),'q_above_0337_margin':float(late.lo),'seconds':time.time()-start}
 Path(__file__).with_name('near_one_binary_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':run()
