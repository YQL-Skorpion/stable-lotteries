"""Outward interval binary proof .9125<=p<=.98 using low slack moments."""
import sys,json,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I
from vector_interval_jets import J,mx,mn
C=lambda s:I(F(s));L=I(C('.562325').lo,C('.562330').hi)
def params(LL,S,c):
 jet=isinstance(S,J);cc=lambda s:J(C(s)) if jet else C(s)
 k=cc('.309');Q=lambda t:LL*t-t.square()/2
 B=lambda t:LL*LL-LL/2+LL*t/2-LL*S/(1-t)
 s=LL/2-c+LL*S/(1-c).square();E=LL*LL-LL/2-LL*c/2+c.square()/2+S*(1-LL/(1-c))
 d0=c+E/s+s/(2*k);t0=d0-s/k
 return LL,cc,k,Q,B,s,E,d0,t0

def select(mask,x,y):
 if isinstance(x,J) or isinstance(y,J):
  x=x if isinstance(x,J) else J(x);y=y if isinstance(y,J) else J(y)
  return J(select(mask,x.v,y.v),[select(mask,a,b) for a,b in zip(x.g,y.g)])
 return I(np.where(mask,x.lo,y.lo),np.where(mask,x.hi,y.hi))

def gap(LL,S,c,q,h,mode=None):
 LL,cc,k,Q,B,s,E,d0,t0=params(LL,S,c)
 v=mx(q,c);w=mn(q,c)
 free=k/2*(mx(d0-q,0).square()-mx(t0-q,0).square())
 el=k/2*(mx(d0-v,0).square()-mx(t0-v,0).square())+S-Q(w)+B(w)-E
 if mode is not None:
  eq=LL*LL-LL/2-LL*q/2+q.square()/2+S*(1-LL/(1-q))
  el=select(mode==1,free,select(mode==-1,eq,el))
 d=mx(cc('.348541')-q-h,0);eu=cc('.000000087')+cc('.00024')*d+k*d.square()/2
 ds=S-cc('.02271790');kap=(cc('2.122')+140*ds+(-cc('3.774')-700*ds)*h)/(1-h)
 return (el-eu)/h.square()-kap*(LL-q)+cc('.5')

def evaluate(block):
 xs=[I(block[:,j],block[:,j+1]) for j in range(0,10,2)]
 LL,cc,k,Q,B,s,E,d0,t0=params(*xs[:3]);feas=((E-s.square()/(2*k)).hi>=0)&(d0.lo<=C('.35945').hi)
 mode=np.where(xs[3].lo>=xs[2].hi,1,np.where(xs[3].hi<=xs[2].lo,-1,0))
 v=gap(*xs,mode=mode);bad=(v.lo<=0)&feas
 scores=(block[:,1::2]-block[:,::2])*np.array([20.,20.,2.,1.,1.])
 if np.any(bad):
  xb=[I(x.lo[bad],x.hi[bad]) for x in xs];jj=gap(*[J.var(x,j) for j,x in enumerate(xb)],mode=mode[bad]);mid=[I((x.lo+x.hi)/2) for x in xb];mv=gap(*mid,mode=mode[bad])
  for j,x in enumerate(xb):mv=mv+jj.g[j]*(x-mid[j])
  v.lo[bad]=np.maximum(v.lo[bad],mv.lo);v.hi[bad]=np.minimum(v.hi[bad],mv.hi)
  for j,x in enumerate(xb):scores[bad,j]=(x.hi-x.lo)*np.maximum(np.abs(jj.g[j].lo),np.abs(jj.g[j].hi))
 return v,feas,np.argmax(scores,axis=1)

def run():
 start=time.time();active=np.array([[float(C('.562325').lo),float(C('.562330').hi),float(C('.02271790').lo),float(C('.023354').hi),float(C('.2918').lo),float(C('.305').hi),float(C('.2918').lo),float(C('.337').hi),float(C('.02').lo),float(C('.0875').hi)]])
 visited=n=excluded=0;floor=np.inf;depth=0
 while len(active):
  parts=[];choices=[]
  for block in np.array_split(active,max(1,(len(active)+199999)//200000)):
   v,feas,which=evaluate(block);visited+=len(block);excluded+=int((~feas).sum());good=feas&(v.lo>0);n+=int(good.sum())
   if good.any():floor=min(floor,float(v.lo[good].min()))
   parts.append(block[feas&~good]);choices.append(which[feas&~good])
  bad=np.vstack(parts);which=np.concatenate(choices)
  print('depth',depth,'visited',visited,'bad',len(bad),'excluded',excluded,'min',floor,'seconds',round(time.time()-start,2),flush=True)
  if not len(bad):break
  assert visited<20000000
  ii=np.arange(len(bad));mid=(bad[ii,2*which]+bad[ii,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ii,2*which+1]=mid;bb[ii,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'mid tail binary interval certificate passed','arithmetic':'outward nextafter arithmetic and first-order interval mean-value intersections','L':['.562325','.562330'],'S':['.02271790','.023354'],'c':['.2918','.305'],'q':['.2918','.337'],'h':['.02','.0875'],'leaves':n,'infeasible_boxes':excluded,'visited':visited,'normalized_gap_lower':floor,'seconds':time.time()-start}
 Path(__file__).with_name('binary_mid_tail_fast_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':run()
