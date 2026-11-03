"""HC beyond .875 on the coupled-contact Hermite completion.

Uses the proved fixed-anchor bounds for every interior binary contact,
all binary constraints, global high concavity, root ceiling, and low shape.
The fixed anchor may extrapolate the quadratic before the true joining rank;
selected-prefix primitive bounds use the true joining deficit instead.
"""
import sys,json,time,argparse
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_structural_large_hc import I,L,S,Qf,B,phi0,headslope,head,lowF

Z=I(Q('.8624')) # Fixed extrapolation anchor, not the true joining rank.
Y=I(I(Q('.08793')).lo,I(Q('.08840')).hi)
H=I(I(Q('-.3589')).lo,I(Q('-.3514')).hi)
h=1-Z
c1=-6*Y/h-4*H+2
c2=3*H-3+6*Y/h
# Backwards tail coordinates, s=1-t.
v=-6*Y/h.square()-2*H/h+4/h;g=-c2/h.square()
# Independently certified coupled-contact coefficient bounds.
v=I(np.maximum(v.lo,I(Q('6.18')).lo),np.minimum(v.hi,I(Q('6.42')).hi))
g=I(np.maximum(g.lo,I(Q('10.77')).lo),np.minimum(g.hi,I(Q('12.73')).hi))
assert min(v.lo,g.lo)>0
assert v.hi<float(I(Q('6.7')).lo)

def tail_phi(t):
    s=1-t
    back=-1+v*s-g*s.square()
    w=1-s/h
    front=H+c1*w+c2*w.square()
    return I(np.maximum(back.lo,front.lo),np.minimum(back.hi,front.hi))

def tail_F(t):
    s=1-t
    back=s-v*s.square()/2+g*s*s*s/3
    w=1-s/h
    front=Y+h*(H*w+c1*w.square()/2+c2*w*w*w/3)
    return I(np.maximum(back.lo,front.lo),np.minimum(back.hi,front.hi))

def tail_combo(t,beta,eta):
    separate=eta*tail_phi(t)-beta*tail_F(t)
    x=(1-t)/h
    xx=x.square();xxx=xx*x
    phH=-2*x+3*xx;phY=(-6*x+6*xx)/h;ph0=-1+4*x-3*xx
    fH=xx-xxx;fY=3*xx-2*xxx;f0=x-2*xx+xxx
    collected=H*(eta*phH-beta*h*fH)+Y*(eta*phY-beta*fY)+eta*ph0-beta*h*f0
    return I(np.maximum(separate.lo,collected.lo),np.minimum(separate.hi,collected.hi))

def choose_pieces(t,parts):
    low=np.full(np.asarray(t.lo).shape,np.inf)
    high=np.full(np.asarray(t.hi).shape,-np.inf)
    for aa,bb,fn in parts:
        a=float(I(Q(aa)).lo);b=float(I(Q(bb)).hi)
        hit=(t.hi>=a)&(t.lo<=b)
        x=I(np.maximum(a,np.minimum(b,t.lo)),np.maximum(a,np.minimum(b,t.hi)))
        z=fn(x)
        low=np.where(hit,np.minimum(low,z.lo),low)
        high=np.where(hit,np.maximum(high,z.hi),high)
    assert np.all(np.isfinite(low)) and np.all(np.isfinite(high))
    return I(low,high)

def price_F(p):
    # On p<=the actual join, integrate phi<=L-t backwards from the join.
    # Overlap both branches on the uncertain join strip.
    def selected(x):
        lo=Qf(x)-S-I(Q('.00290'))
        hi=Qf(x)-S
        return I(lo.lo,hi.hi)
    return choose_pieces(p,[('.562325','.782',lambda x:Qf(x)-S),
                           ('.782','.875',selected),
                           ('.8495','1',tail_F)])

def upper_F(t):
    # Root budget supplies a valid upper bound through the whole high arc.
    def freeupper(x):
        d=I(Q('.34854007977695545'))-x
        near=Qf(x)-S+I(Q('.000000087'))+I(Q('.00024'))*d+I(Q('.309'))*d.square()/2
        cap=B(x)
        return I(np.minimum(near.lo,cap.lo),np.minimum(near.hi,cap.hi))
    return choose_pieces(t,[('0','.313',lowF),('.313','.34854007977695545',freeupper),
          ('.34854007977695545','.36',lambda x:Qf(x)-S+I(Q('.000000087'))),
          ('.36','.875',lambda x:Qf(x)-S),('.8495','1',tail_F)])

def lower_phi(t):
    def freelower(x):
        fromtail=L-x-I(Q('.00024'))-I(Q('.309'))*(I(Q('.34854007977695545'))-x)
        rational=L/2-L*S/(1-x).square()
        # Before the unknown cap contact use the rational score. After it,
        # integrate sigma'>=-.309 backwards from the retained endpoint.
        either=I(np.minimum(fromtail.lo,rational.lo),np.minimum(fromtail.hi,rational.hi))
        coarse=L-x-I(Q('.022'))
        return I(np.maximum(either.lo,coarse.lo),np.maximum(either.hi,coarse.hi))
    return choose_pieces(t,[('0','.2635',lambda x:phi0+headslope*x),
          ('.2635','.2918',lambda x:L/2-L*S/(1-x).square()),
          ('.2918','.34854007977695545',freelower),
          ('.34854007977695545','.36',lambda x:L-x-I(Q('.00024'))),
          ('.36','.782',lambda x:L-x),
          ('.782','.875',lambda x:I(np.full(np.asarray(x.lo).shape,float(I(Q('-.429')).lo)))),
          ('.8495','1',tail_phi)])

def prices(p,intermediate):
    fp=price_F(p)
    # At broad initial boxes, plain interval dependency can lose positivity;
    # retain the independent integrated-root-ceiling lower bound.
    rootlower=(1-p)*((1+p)/2-L)
    fp=I(np.maximum(fp.lo,rootlower.lo),fp.hi)
    be=p/fp
    if intermediate:
        rr=1-p
        P=choose_pieces(rr,[('.34','.36',lowF),('.36','.438',lambda x:Qf(x)-S)])
        ci=L-be*P
        eta=1+I(np.maximum(0.,ci.lo),np.maximum(0.,ci.hi))/(L/2-L*S/(1-head).square())
    else:eta=I(np.ones(np.asarray(p.lo).shape))
    return be,eta

def evaluate(box,intermediate):
    p,q,z=[I(box[:,2*j],box[:,2*j+1]) for j in range(3)]
    be,eta=prices(p,intermediate)
    delay=z-p+q
    delay=I(np.maximum(0.,delay.lo),np.minimum(1.,delay.hi))
    K=upper_F(delay)-lowF(q)
    collected=q+z-L+be*K+tail_combo(z,be,eta)
    direct=q+z-L+be*(K-tail_F(z))+eta*tail_phi(z)
    C=I(np.maximum(collected.lo,direct.lo),np.minimum(collected.hi,direct.hi))
    # If q is in the affine head and q+z-p in the central segment, the
    # entire q dependence is a concave quadratic. Its unconstrained
    # maximum is an upper bound and avoids repeated q occurrences.
    headcase=(q.hi<=float(head.lo))&(delay.lo>=float(I(Q('.36')).hi))&(delay.hi<=float(I(Q('.782')).lo))
    d=z-p
    lin=1+be*(L-d-phi0)
    pos=I(np.maximum(0.,lin.lo),np.maximum(0.,lin.hi))
    quad=be*(1+headslope)
    assert np.all(quad.lo>0)
    hm=z-L+tail_combo(z,be,eta)+be*(Qf(d)-S)+pos.square()/(2*quad)
    C=I(C.lo,np.where(headcase,np.minimum(C.hi,hm.hi),C.hi))
    # Compare actual C(q,z) to its binary face C(q,1), using derivatives
    # over the entire future tail interval, never a reference corner.
    ZZ=I(z.lo,np.ones(z.lo.shape));dd=ZZ-p+q
    dd=I(np.maximum(0.,dd.lo),np.minimum(1.,dd.hi))
    ph=lower_phi(dd)
    gz=1+be*(ph-tail_phi(ZZ))-eta*I(Q('6.7'))
    binary=(z.lo>=float(I(Q('.95')).hi))&(gz.lo>=0)
    # Binary gives q-L+be*Delta<=0; eta>=1 only lowers the face.
    return C.hi,binary

def run():
    ap=argparse.ArgumentParser();ap.add_argument('--intermediate',action='store_true');ap.add_argument('--max-boxes',type=int,default=5000000);args=ap.parse_args()
    pl='.562325' if args.intermediate else '.65'
    pr='.65' if args.intermediate else '.925'
    active=np.array([[float(I(Q(pl)).lo),float(I(Q(pr)).hi),0.,float(L.hi),float(I(Q('.875')).lo),1.]])
    visited=leaves=nbinary=0;worst=-np.inf;start=time.time();depth=0
    while len(active):
        active=active[active[:,5]>=active[:,0]]
        active[:,1]=np.minimum(active[:,1],active[:,5])
        active[:,4]=np.maximum(active[:,4],active[:,0])
        up,binary=evaluate(active,args.intermediate);visited+=len(active)
        direct=up<0;good=direct|binary
        if np.any(direct):worst=max(worst,float(np.max(up[direct])))
        leaves+=int(np.sum(good));nbinary+=int(np.sum(binary));bad=active[~good]
        print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'upper':float(np.max(up)),'seconds':time.time()-start}),flush=True)
        if not len(bad):break
        if visited>args.max_boxes:raise RuntimeError('box budget exceeded')
        widths=bad[:,1::2]-bad[:,::2]
        which=np.argmax(widths*np.array([6.,3.,8.]),axis=1)
        ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
        assert np.max(widths)>1e-8,'remaining intrinsic bound failure'
        left=bad.copy();right=bad.copy();left[ids,2*which+1]=mid;right[ids,2*which]=mid
        active=np.vstack([left,right]);depth+=1
    out={'status':'verified structural Hermite-tail HC from coupled-contact bounds and binary',
         'intermediate':args.intermediate,'p_range':[pl,pr],'z_range':['max(p,.875)','1'],
         'q_range':['0','L'],'L_range':['.562325','.562330'],'S_range':['.02271790','.023354'],
         'fixed_anchor_box':{'anchor':'.8624','Y':['.08793','.08840'],'H':['-.3589','-.3514']},
         'true_join_range':['.8495','.875'],'coupled_contact_certificate':'global/fixed_anchor_terminal_certificate.json',
         'visited':visited,'leaves':leaves,'binary_face_boxes':nbinary,'strict_direct_HC_upper':worst,
         'completion':'q>=L follows from high concavity','seconds':time.time()-start}
    suffix='intermediate' if args.intermediate else 'large'
    Path(__file__).with_name('structural_tail_hc_'+suffix+'_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':run()
