"""Outward interval sharp diagonal slope on the enlarged terminal strip.
Analytic endpoint/quadratic reduction is verify_diagonal_slope_band.py's.
Here N_A is directly checked in every interval box for both B endpoints.
"""
import argparse, json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from interval_warped_hessian import I

def evaluate(boxes,gap,slope):
 L,S,r,a=[I(boxes[:,2*j],boxes[:,2*j+1]) for j in range(4)]
 h=2*L-a;k=2*r-L;p=1-r-L
 Q=lambda t:L*t-t*t/2
 P=Q(1-r)-S;B=L-r-gap
 As=[L-a,L/2-L*S/I(F('.72')).square()]
 lower=np.full(len(boxes),np.inf);na_hi=np.full(len(boxes),-np.inf)
 for z in [I(F('.775')),I(F('.875'))]:
  U=z-L;d=r-U
  for R in [Q(r)-S,L*P/(1-r)]:
   D=h*R-k*P
   for K in [r*(U-r/2),r*(U-r/2)+L-I(F('.5'))-S]:
    cA=U*R+k*K;cB=U*P+h*K
    assert np.all(D.lo>0) and np.all(cA.lo>0) and np.all(cB.lo>0)
    # N_A is affine in B and independent of A. Certify on full B interval.
    for BB in [B,L-r]:
     na=k*(BB*cB-cA*p+d*D)-2*R*cB
     na_hi=np.maximum(na_hi,na.hi)
    tnum=B*cB-cA*p+d*D
    best=np.full(len(boxes),-np.inf)
    for A in As:
     J=k*A+h*B
     N=cB*(slope*D-2*A*R-2*B*P)+J*tnum
     NB=2*h*B*cB+k*A*cB-h*cA*p+h*d*D-2*P*cB
     neg=I(np.maximum(0.,-NB.hi),np.maximum(0.,-NB.lo))
     best=np.maximum(best,(N-neg.square()/(4*h*cB)).lo)
    lower=np.minimum(lower,best)
 return lower,na_hi

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--gap',default='.00024');ap.add_argument('--slope',default='.978');ap.add_argument('--rmin',default='.34854007977695545');ap.add_argument('--rmax',default='.36');ap.add_argument('--amin',default='.2918');ap.add_argument('--smin',default='.02271790');ap.add_argument('--smax',default='.023354');ap.add_argument('--output',default='research/closure/global/tail_diagonal_extension_certificate.json');args=ap.parse_args()
 dom=[('.562325','.562330'),(args.smin,args.smax),(args.rmin,args.rmax),(args.amin,args.rmax)]
 flat=[]
 for lo,hi in dom:flat.extend([float(I(F(lo)).lo),float(I(F(hi)).hi)])
 active=np.array([flat]);widths0=np.array(flat[1::2])-np.array(flat[::2]);visited=verified=depth=0;least=np.inf;maxna=-np.inf
 while len(active):
  lo,na=evaluate(active,I(F(args.gap)),I(F(args.slope)));visited+=len(active);good=(lo>0)&(na<0)
  if np.any(good):least=min(least,float(np.min(lo[good])));maxna=max(maxna,float(np.max(na[good])))
  verified+=int(np.sum(good));bad=active[~good]
  print(json.dumps({'depth':depth,'tested':len(active),'remaining':len(bad),'visited':visited,'lower':float(np.min(lo)),'na_upper':float(np.max(na))}),flush=True)
  if not len(bad):break
  if visited>4000000:raise RuntimeError('box budget exhausted')
  widths=(bad[:,1::2]-bad[:,::2])/widths0;widths[:,0]*=.002;which=np.argmax(widths,axis=1)
  mid=(bad[np.arange(len(bad)),2*which]+bad[np.arange(len(bad)),2*which+1])/2
  left=bad.copy();right=bad.copy();left[np.arange(len(bad)),2*which+1]=mid;right[np.arange(len(bad)),2*which]=mid
  active=np.vstack([left,right]);active=active[active[:,6]<=active[:,5]];depth+=1
 out={'status':'verified conditional diagonal slope > -'+args.slope,'ceiling_slack_upper':args.gap,'domain':dom,'visited':visited,'verified_boxes':verified,'positive_numerator_lower_across_leaves':least,'negative_A_derivative_numerator_upper':maxna}
 Path(args.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
