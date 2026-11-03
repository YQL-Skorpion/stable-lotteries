"""Structural binary certificate .65<=p<=.775, using c_last<.305."""
import json,time
import numpy as np
from pathlib import Path
from certify_structural_intermediate import I,C,L,b,c,Q,rat,rp,head,head0,primitive
S=I(C('.02271790').lo,C('.023354').hi);cc=C('.305');rc=C('.348541')
f0=head0(S);sl=(rp(b,S)-f0)/b

def upperF(x):
 base=primitive(x,S,True)
 d=x-cc
 quad=rat(cc,S)+rp(cc,S)*d-C('.691')*d.square()/2
 dd=I(np.maximum(0.,(rc-x).lo),np.maximum(0.,(rc-x).hi))
 cone=Q(x)-S+C('.000000087')+C('.00024')*dd+C('.309')*dd.square()/2
 hi=base.hi
 hi=np.where(x.lo>=cc.hi,np.minimum(hi,quad.hi),hi)
 hi=np.where(x.lo>=C('.313').hi,np.minimum(hi,cone.hi),hi)
 return I(hi)

def upperphi(x):
 shape=x.lo.shape;ans=np.full(shape,-np.inf)
 for left,right,kind in [(0.,float(b.hi),0),(float(b.lo),float(cc.hi),1),(float(cc.lo),1.,2)]:
  hit=(x.hi>=left)&(x.lo<=right);xx=I(np.maximum(left,np.minimum(right,x.lo)),np.maximum(left,np.minimum(right,x.hi)))
  v=f0+sl*xx if kind==0 else rp(xx,S) if kind==1 else I(np.minimum((L-xx).hi,(rp(cc,S)-C('.691')*(xx-cc)).hi))
  ans=np.where(hit,np.maximum(ans,v.hi),ans)
 return I(ans)

def run():
 global S,f0,sl
 start=time.time();active=np.array([[float(C('.02271790').lo),float(C('.023354').hi),float(C('.65').lo),float(C('.775').hi),0.,float(C('.18').hi)]])
 visited=leaves=qzero=0;worst=-np.inf;depth=0
 while len(active):
  S,p,q=[I(active[:,j],active[:,j+1]) for j in range(0,6,2)];f0=head0(S);sl=(rp(b,S)-f0)/b;h=1-p;Fp=Q(p)-S;t=h+q
  # Algebraically factor the exact rational cap residual by q.
  g=Fp+p*(L/2-f0-sl*q/2)-L*S/(p-q)
  d=t-cc;dd=I(np.maximum(0.,d.lo),np.maximum(0.,d.hi))
  rational=L*S/((1-cc).square()*(1-t))
  capdiff=dd.square()*(rational-C('.691')/2)
  sigma=L-cc-rp(cc,S)
  # Ecap(cc), expanded to preserve the small deficit under intervals.
  Ecap=L*L-L/2-L*cc/2+cc.square()/2+S*(1-L/(1-cc))
  back=I(np.maximum(0.,(rc-t).lo),np.maximum(0.,(rc-t).hi))
  conediff=C('.000000087')+C('.00024')*back+C('.309')*back.square()/2-Ecap+sigma*d-d.square()/2+rational*d.square()
  dhi=np.minimum(0.,capdiff.hi)
  dhi=np.where(t.lo>=cc.hi,np.minimum(dhi,conediff.hi),dhi)
  # capdiff is used only for t>=cc; its zero extension remains valid below.
  value=q*g+p*I(dhi)
  nonpositive=(g.hi<0)&(dhi<=0)
  good=nonpositive|(value.hi<0);visited+=len(active);leaves+=int(np.sum(good));qzero+=int(np.sum(nonpositive))
  strict=good&~nonpositive
  if np.any(strict):worst=max(worst,float(np.max(value.hi[strict])))
  bad=active[~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'qzero':qzero,'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  assert visited<12000000
  widths=bad[:,1::2]-bad[:,::2];which=np.argmax(widths*np.array([20.,2.,2.]),axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'structural central binary passed','p':['.65','.775'],'q':['0','.18'],'visited':visited,'leaves':leaves,'q0_factor_boxes':qzero,'binary_upper_on_strict_boxes':worst,'seconds':time.time()-start,
 'q0':'F(1-p)<=B_S(1-p), matched head below B; F(p)=Q(p)-S',
 'remaining_q':'derivative at q=.18 is negative and nonincreasing thereafter; separate exact constant check'}
 Path(__file__).with_name('structural_binary_central_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
if __name__=='__main__':run()
