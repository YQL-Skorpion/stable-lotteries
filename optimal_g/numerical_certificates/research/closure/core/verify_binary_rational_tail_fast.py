"""Outward-rounded vector interval certificate for rational-tail curvature."""
import sys,json,time
from pathlib import Path
from fractions import Fraction as F
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I
from vector_interval_jets import J
C=lambda x:I(F(x));L=I(C('.562325').lo,C('.562330').hi)
def pq(S,q):
 LL=J(L) if isinstance(S,J) else L
 Llocal=LL
 sig=Llocal/2-q+Llocal*S/(1-q).square()
 E=Llocal*Llocal-Llocal/2-Llocal*q/2+q.square()/2+S*(1-Llocal/(1-q))
 h2=2*(Llocal-q)*sig-2*E
 if np.any((h2.v if isinstance(h2,J) else h2).lo<=0):return None
 return 1-h2.sqrt(),sig

def curvature(S,qc,u):
 LL=J(L) if isinstance(S,J) else L
 cc=J(C('.2918')) if isinstance(S,J) else C('.2918')
 pair=pq(S,qc)
 if pair is None:return None
 zc,sc=pair;hc=1-zc;Y=zc*(hc-sc);H=1-2*zc-sc+zc*hc/(LL-qc)
 c1=-6*Y/hc-4*H+2;c2=3*H-3+6*Y/hc
 q=qc+u*(cc-qc);pair=pq(S,q)
 if pair is None:return None
 p,sig=pair;h=1-p
 rat=-2+(2-3*p)/(LL-q)+p*h.square()/((LL-q).square()*(LL-q)*(1-2*LL*S/((1-q).square()*(1-q))))
 her=(c1+2*c2*(p-zc)/hc)/hc
 return her-rat

def evaluate(block):
 xs=[I(block[:,j],block[:,j+1]) for j in range(0,6,2)]
 v=curvature(*xs)
 if v is None:return None
 bad=v.lo<=0
 if np.any(bad):
  xb=[I(x.lo[bad],x.hi[bad]) for x in xs];jj=curvature(*[J.var(x,j) for j,x in enumerate(xb)])
  mids=[I((x.lo+x.hi)/2) for x in xb];mv=curvature(*mids)
  for j,x in enumerate(xb):mv=mv+jj.g[j]*(x-mids[j])
  v.lo[bad]=np.maximum(v.lo[bad],mv.lo);v.hi[bad]=np.minimum(v.hi[bad],mv.hi)
 return v

def run():
 start=time.time();active=np.array([[float(C('.02271790').lo),float(C('.023354').hi),float(C('.2635').lo),float(C('.2764').hi),0.,1.]])
 n=visited=0;floor=np.inf;depth=0
 while len(active):
  v=evaluate(active);good=np.zeros(len(active),dtype=bool) if v is None else v.lo>0
  n+=int(good.sum());visited+=len(active)
  if good.any():floor=min(floor,float(v.lo[good].min()))
  bad=active[~good]
  print('depth',depth,'visited',visited,'bad',len(bad),'min',floor,'seconds',round(time.time()-start,2),flush=True)
  if not len(bad):break
  assert visited<10000000
  which=np.argmax((bad[:,1::2]-bad[:,::2])*np.array([20.,1.,.02]),axis=1);ii=np.arange(len(bad));mid=(bad[ii,2*which]+bad[ii,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ii,2*which+1]=mid;bb[ii,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'rational-tail curvature interval certificate passed','arithmetic':'outward nextafter after each operation; exact rational decimal inputs enclosed; outward sqrt; first-order interval mean-value intersection','L':['.562325','.562330'],'S':['.02271790','.023354'],'q_contact':['.2635','.2764'],'q_upper':'.2918','leaves':n,'visited':visited,'curvature_gap_lower':floor,'seconds':time.time()-start}
 Path(__file__).with_name('binary_rational_tail_fast_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':run()
