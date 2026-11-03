"""Outward arithmetic for structural dual extension on p in [.04,.2635].
See structural_left_extension.txt for envelope differentiation and endpoint use.
"""
import json,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from interval_warped_hessian import I
C=lambda x:I(F(x))
def quantities(box):
 L,S,p=[I(box[:,2*j],box[:,2*j+1]) for j in range(3)]
 hb=C('.2635');Q=lambda t:L*t-t.square()/2
 B=lambda t:L*L-L/2+L*t/2-L*S/(1-t)
 fp=lambda t:L/2-L*S/(1-t).square()
 f0=2*B(hb)/hb-fp(hb);slope=(fp(hb)-f0)/hb
 R=f0*p+slope*p.square()/2;Rp=f0+slope*p
 P=Q(1-p)-S;Pp=1-p-L;V=R+P
 beta=(L+p)/V;bp=(V-(L+p)*(Rp+Pp))/V.square()
 m=2*L-beta*P;mp=-bp*P-beta*Pp
 M=fp(C('.28'));a0=C('.2918');etaup=(m-a0)/fp(a0)
 return L,S,p,f0,slope,R,P,beta,bp,m,mp,M,etaup,fp(hb)
def evaluate(box,kind):
 L,S,p,f0,slope,R,P,be,bp,m,mp,M,etaup,fh=quantities(box)
 if kind=='direct':
  e1=1+be*p;e2=1+(m-L)/M
  eta=I(np.minimum(e1.lo,e2.lo),np.minimum(e1.hi,e2.hi))
  gap=1+be*p-eta
  # Use an upper bound for gap; it is analytically nonnegative.
  at788=(C('.789')-L)*gap-be*p.square()/2
  at1=(1-L)*gap-be*p.square()/2+(be*C('.109')-eta)*C('.26')*C('.211')
  checks=[(m-L).lo,(m-eta*f0).lo,(eta-be*C('.109')).lo,-at788.hi,-at1.hi]
  # Rational support a+eta phi(a) increases between head and .28.
  curvature=2*L*S/C('.72').pow(3) if hasattr(C('.72'),'pow') else 2*L*S/(C('.72')*C('.72')*C('.72'))
  checks.extend([(1-eta*curvature).lo,(eta-1).lo])
 else:
  Amax=f0 if kind=='derivative_head' else M
  tt=-mp/Amax
  vv=tt+bp*p+be
  aton=(C('.782')-L)*vv-bp*p.square()/2-be*p
  at1=tt+bp*((1-L)*p-p.square()/2+L*C('.109'))+be*(1-L-p)
  checks=[-bp.hi,-mp.hi,vv.lo,aton.lo,at1.lo,(1+be*p-etaup).lo]
  if kind=='derivative_low':
   checks.extend([(m-etaup*f0).lo,(1-etaup*2*L*S/(C('.7082')*C('.7082')*C('.7082'))).lo])
 # q=0 controls A and high C; low B follows eta<=1+beta p.
 checks.extend([(be*(fh-(L-1+p))-1).lo,(be*(f0-L+C('.782')-p)-1).lo])
 return np.minimum.reduce(checks)
def run_kind(kind,pl,ph):
 dom=[('.562325','.562330'),('.02271790','.023354'),(pl,ph)];flat=[]
 for a,b in dom:flat.extend([float(C(a).lo),float(C(b).hi)])
 active=np.array([flat]);visited=leaves=depth=0;least=np.inf
 width0=np.array(flat[1::2])-np.array(flat[::2])
 while len(active):
  margins=evaluate(active,kind);visited+=len(active);good=margins>0
  if np.any(good):least=min(least,float(np.min(margins[good])))
  leaves+=int(np.sum(good));bad=active[~good]
  print(json.dumps({'kind':kind,'depth':depth,'visited':visited,'remaining':len(bad),'min_margin':float(np.min(margins))}),flush=True)
  if not len(bad):break
  if visited>3000000:raise RuntimeError('box budget')
  widths=(bad[:,1::2]-bad[:,::2])/width0;widths[:,0]*=.02;which=np.argmax(widths,axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  a=bad.copy();b=bad.copy();a[ids,2*which+1]=mid;b[ids,2*which]=mid;active=np.vstack([a,b]);depth+=1
 return {'kind':kind,'domain':dom,'visited':visited,'leaves':leaves,'minimum_positive_margin':least}
def main():
 # Selected fixed rational-root cut forces departure strictly before .789.
 boxes=np.array([[float(C('.562325').lo),float(C('.562330').hi),float(C('.02271790').lo),float(C('.023354').hi),float(C('.27').lo),float(C('.27').hi)]])
 # Subdivide S for a sharp rational interval onset enclosure.
 top=-np.inf
 for j in range(64):
  L=I(C('.562325').lo,C('.562330').hi);S=I((C('.02271790')+(C('.023354')-C('.02271790'))*C(str(F(j,64)))).lo,(C('.02271790')+(C('.023354')-C('.02271790'))*C(str(F(j+1,64)))).hi)
  r=C('.27');a=C('.2918');Q=lambda t:L*t-t.square()/2
  R=L*(Q(1-r)-S)/(1-r);P=Q(1-r)-S;A=L/2-L*S/(1-a).square()
  D=(2*L-a)*R-(r+a-L)*P;cc=A*(R+P)/D;al=(r+L)*A/D;mm=cc-1+al*r
  assert np.all(D.lo>0) and np.all(mm.lo>0)
  cross=L+al*r.square()/(2*mm);top=max(top,float(cross.hi))
 assert top<float(C('.789').lo),top
 out={'status':'structural left dual coefficient certificate passed','head':'.2635','selected_boundary':'.2635','onset_upper_from_r027_cut':top,'onset_lower':'.782','high_slope_excess':'.26','parts':[run_kind('direct','.04','.14'),run_kind('derivative_head','.14','.20'),run_kind('derivative_low','.20','.2635')]}
 Path(__file__).with_name('structural_left_extension_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
