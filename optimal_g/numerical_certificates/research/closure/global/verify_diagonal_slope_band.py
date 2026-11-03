"""Outward interval certificate for a diagonal-root slope invariant band.

The analytic reduction makes the numerator multilinear in R, K and z.
The remaining four-dimensional boxes are refined adaptively. This proves
an algebraic bound conditional on the explicitly stated score band; it does
not establish the normal-form, coverage or initial-band hypotheses.
"""
import argparse
from fractions import Fraction as F
import json
import numpy as np
from pathlib import Path
from interval_warped_hessian import I


def evaluate(boxes, gap):
    vals=[I(boxes[:,2*j],boxes[:,2*j+1]) for j in range(4)]
    L,S,r,a=vals
    h=2*L-a;k=2*r-L;p=1-r-L
    Q=lambda t:L*t-t*t/2
    P=Q(1-r)-S
    Rends=[Q(r)-S,L*P/(1-r)]
    B=L-r-gap
    As=[L-a,L/2-L*S/I(F('.72')).square()]
    lower=np.full(len(boxes),np.inf)
    dmin=np.full(len(boxes),np.inf)
    for z in [I(F('.775')),I(F('.875'))]:
        U=z-L;d=r-U
        for R in Rends:
            D=h*R-k*P
            dmin=np.minimum(dmin,D.lo)
            for K in [r*(U-r/2),r*(U-r/2)+L-I(F('.5'))-S]:
                cA=U*R+k*K;cB=U*P+h*K
                assert np.all(cA.lo>0) and np.all(cB.lo>0) and np.all(D.lo>0)
                tnum=B*cB-cA*p+d*D
                best=np.full(len(boxes),-np.inf)
                for A in As:
                    J=k*A+h*B
                    N=cB*(D-2*A*R-2*B*P)+J*tnum
                    NB=2*h*B*cB+k*A*cB-h*cA*p+h*d*D-2*P*cB
                    neg=I(np.maximum(0.,-NB.hi),np.maximum(0.,-NB.lo))
                    quadratic_lower=N-neg.square()/(4*h*cB)
                    best=np.maximum(best,quadratic_lower.lo)
                lower=np.minimum(lower,best)
    return lower,dmin


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--gap',default='.022')
    parser.add_argument('--r-min',default='.29')
    parser.add_argument('--r-max',default='.35')
    parser.add_argument('--max-boxes',type=int,default=6000000)
    parser.add_argument('--output',default='research/closure/global/diagonal_slope_band_certificate.json')
    args=parser.parse_args()
    gap=I(F(args.gap))
    # N_A<0 on the whole coarse domain, independently of the score band.
    na_upper=F('.03481295')*(F('.138')*F('.27733')-2*F('.0857'))+F('.138')*F('.137675')*F('.116')
    assert na_upper<0
    endpoints=[('.562325','.562330'),('.0219728','.0266504'),(args.r_min,args.r_max),('.285',args.r_max)]
    flat=[]
    for lo,hi in endpoints:flat.extend([float(I(F(lo)).lo),float(I(F(hi)).hi)])
    active=np.array([flat]);verified=0;visited=0;depth=0;least=np.inf
    # L is extremely narrow already. Refine S,r,a; optionally split L once.
    widths0=np.array([hi-lo for lo,hi in zip(flat[::2],flat[1::2])])
    while len(active):
        lows,ds=evaluate(active,gap)
        visited+=len(active)
        good=lows>0
        if np.any(good):least=min(least,float(np.min(lows[good])))
        verified+=int(np.sum(good))
        bad=active[~good]
        print(json.dumps({'depth':depth,'tested':len(active),'remaining':len(bad),'visited':visited,'lower':float(np.min(lows))}),flush=True)
        if not len(bad):break
        if visited>args.max_boxes:raise RuntimeError('box budget exhausted')
        # Balanced refinement of the three nontrivial coordinate widths.
        normalized=(bad[:,1::2]-bad[:,::2])/widths0
        normalized[:,0]*=.002
        which=np.argmax(normalized,axis=1)
        mid=(bad[np.arange(len(bad)),2*which]+bad[np.arange(len(bad)),2*which+1])/2
        left=bad.copy();right=bad.copy()
        left[np.arange(len(bad)),2*which+1]=mid
        right[np.arange(len(bad)),2*which]=mid
        active=np.vstack([left,right])
        # Only the late a<=r case requires diagonal slope analysis.
        active=active[active[:,6]<=active[:,5]]
        depth+=1
    out={'status':'verified conditional diagonal slope > -1','score_slack_band':args.gap,'domain':endpoints,'visited':visited,'verified_boxes':verified,'positive_numerator_lower_across_leaves':least,'negative_A_derivative_numerator_upper':str(na_upper)}
    Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':main()
