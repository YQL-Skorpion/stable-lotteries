"""Right-layer comparison using the actual support line at p0=.36.
Only the selected high arc is considered here; E<=.00290 is a prerequisite.
"""
from fractions import Fraction as F
from pathlib import Path
import json,time,argparse
import numpy as np
from interval_warped_hessian import I
C=lambda t:I(F(t))
L=I(C('.562325').lo,C('.562330').hi);p0=C('.36');hb=C('.2635');cc=C('.2918');rc=C('.34854007977695545')
Q=lambda t:L*t-t.square()/2

def data(S):
 B=lambda t:L*L-L/2+L*t/2-L*S/(1-t)
 ph=lambda t:L/2-L*S/(1-t).square()
 f0=2*B(hb)/hb-ph(hb);sl=(ph(hb)-f0)/hb
 return B,ph,f0,sl

def piece(t,S,mode):
 B,ph,f0,sl=data(S)
 lo=np.full(np.broadcast_shapes(t.lo.shape,S.lo.shape),np.inf);hi=np.full(lo.shape,-np.inf)
 domains=[('0','.2635','head'),('.2635','.2918','prefix'),('.2918','.313','free1'),('.313','.34854007977695545','free2'),('.34854007977695545','.36','late'),('.36','.782','central'),('.782','1','high')]
 for aa,bb,kind in domains:
  a=float(C(aa).lo);b=float(C(bb).hi);xlo=np.maximum(t.lo,a);xhi=np.minimum(t.hi,b);hit=xlo<=xhi
  x=I(np.where(hit,xlo,a),np.where(hit,xhi,a))
  if mode=='slackupper':
   if kind=='head':v=(L-f0)*x-(1+sl)*x.square()/2
   elif kind=='prefix':v=Q(x)-B(x)
   elif kind in ['free1','free2','late']:
    ec=S-Q(cc)+B(cc);sc=L-cc-ph(cc);rem=ec-sc*(x-cc)
    v=S-I(np.maximum(0.,rem.lo),np.maximum(0.,rem.hi))
   else:v=S
  elif mode=='remainingupper':
   if kind=='head':v=S-(L-f0)*x+(1+sl)*x.square()/2
   elif kind in ['prefix','free1']:v=S-Q(x)+B(x)
   elif kind=='free2':
    near=C('.000000087')+C('.00024')*(rc-x)+C('.309')*(rc-x).square()/2;cap=S-Q(x)+B(x)
    v=I(np.minimum(near.lo,cap.lo),np.minimum(near.hi,cap.hi))
   elif kind=='late':v=C('.000000087')
   else:v=I(np.zeros(x.lo.shape))
  else:
   if kind=='head':v=f0+sl*x
   elif kind=='prefix':v=ph(x)
   elif kind in ['free1','free2']:
    near=L-x-C('.00024')-C('.309')*(rc-x);rational=ph(x);coarse=L-x-C('.022')
    lower=np.maximum(coarse.lo,np.minimum(near.lo,rational.lo));M=ph(C('.28'))
    v=I(lower,np.minimum(M.hi,(L-x).hi))
   elif kind=='late':v=I((L-x-C('.00024')).lo,(L-x).hi)
   elif kind=='central':v=L-x
   else:v=I(np.full(x.lo.shape,-.429),(L-x).hi)
  lo=np.where(hit,np.minimum(lo,v.lo),lo);hi=np.where(hit,np.maximum(hi,v.hi),hi)
 assert np.all(np.isfinite(lo)) and np.all(np.isfinite(hi))
 return I(lo,hi)

def prices(S,p,tau):
 A=L-tau;h=2*L-tau;R=Q(p)-S;P=Q(1-p)-S;k=2*p-L
 N=A*R+(L-p)*P;D=h*R-k*P;J=L.square()-tau*p
 R0=Q(p0)-S;P0=Q(1-p0)-S;k0=2*p0-L
 N0=A*R0+(L-p0)*P0;D0=h*R0-k0*P0;J0=L.square()-tau*p0
 delta=p-p0;rr=L-p0-delta/2;pp=1-p0-L-delta/2
 n1=A*rr+(L-p0)*pp-P0-delta*pp
 d1=h*rr-k0*pp-2*P0-2*delta*pp
 w=-tau*D0-d1*J0
 eta=D/N;beta=J/N
 Rp=L-p;Pp=1-p-L;Np=A*Rp-P+(L-p)*Pp;Dp=h*Rp-2*P-k*Pp
 ep=(Dp*N-D*Np)/N.square()
 return N,D,J,N0,D0,J0,n1,d1,w,eta,beta,ep

def evaluate(box,local=False):
 S,p,q,z,tau=[I(box[:,2*j],box[:,2*j+1]) for j in range(5)]
 N,D,J,N0,D0,J0,n1,d1,w,eta,beta,ep=prices(S,p,tau)
 U=z-L;delta=p-p0;K0=p0*(U-p0/2)
 T1=(n1*D0-d1*N0)*U+J*D0*(U-p0-delta/2)+w*K0+C('.00290')*I(np.maximum(0.,w.lo),np.maximum(0.,w.hi))
 common=(eta-1).lo>0
 common&=(ep.hi<0)&(N.lo>0)&(D.lo>0)&(J.lo>0)&((1+beta*p-eta).lo>0)
 _,_,f0,_=data(S)
 common&=(beta*(f0-L+1-p)-1).lo>0
 if local:
  _,_,f0,_=data(S)
  split=beta*(f0-L+C('.782')-p)-1
  return T1.hi,common&(split.lo>0)
 su=piece(q,S,'slackupper');eu=piece(z-p+q,S,'remainingupper')
 residual=delta*T1+D0*(q*(N-J*(z-p))+J*(su+eu))
 return residual.hi,common

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--local',action='store_true');ap.add_argument('--max-boxes',type=int,default=12000000);args=ap.parse_args()
 pl,ph=('.36','.38') if args.local else ('.38','.562330')
 flat=[]
 for a,b in [('.02271790','.023354'),(pl,ph),('0','.562330'),('.782','.875'),('.3058','.36')]:flat.extend([float(C(a).lo),float(C(b).hi)])
 if args.local:flat[4]=flat[5]=0.
 active=np.array([flat]);start=time.time();visited=leaves=depth=0;worst=-np.inf
 while len(active):
  active=active[active[:,4]<=active[:,3]]
  active[:,5]=np.minimum(active[:,5],active[:,3]);active[:,2]=np.maximum(active[:,2],active[:,4])
  if not args.local:
   for _ in range(2):
    S,p,q,z,tau=[I(active[:,2*j],active[:,2*j+1]) for j in range(5)]
    beta=prices(S,p,tau)[10];dq=1+beta*(piece(z-p+q,S,'score')-piece(q,S,'score'))
    inc=dq.lo>=0;dec=dq.hi<=0
    active[:,4]=np.where(inc,active[:,5],active[:,4]);active[:,5]=np.where(dec,active[:,4],active[:,5])
  up,valid=evaluate(active,args.local);good=(up<0)&valid;visited+=len(active);leaves+=int(np.sum(good))
  if np.any(good):worst=max(worst,float(np.max(up[good])))
  bad=active[~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'max_upper':float(np.max(up)),'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  if visited>args.max_boxes:raise RuntimeError('box budget')
  widths=bad[:,1::2]-bad[:,::2];weights=np.array([30.,5.,5.,6.,10.]);which=np.argmax(widths*weights,axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'verified right support-line selected-high comparison','local':args.local,'p_range':[pl,ph],'z_range':['.782','.875'],'tau_range':['.3058','.36'],'S_range':['.02271790','.023354'],'E_upper':'.00290','visited':visited,'leaves':leaves,'strict_cleared_upper':worst,'seconds':time.time()-start}
 suffix='local' if args.local else 'global';Path(__file__).with_name('right_support_transport_'+suffix+'_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
