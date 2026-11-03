"""Structural HC certificate through high rank .875 for p>=.65.

No nodal-reference neighborhood is assumed. Hypotheses: proved low shape,
affine head .2635, rational prefix through .2918, contact before .36,
high central through .782 and concavity, fixed cut r=a=b=.34854,
sigma(rc)<.00024, free sigma' >=-.309, and the global root ceiling with
F(1)=0. Cap preservation extends this proof across an earlier Hermite join.
Ranks above .875 are covered by a separate explicit tail certificate.
"""
import sys,json,time
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I

L=I(I(Q('.562325')).lo,I(Q('.562330')).hi)
S=I(I(Q('.02271790')).lo,I(Q('.023354')).hi)
head=I(Q('.2635'));prefix=I(Q('.2918'));rc=I(Q('.348541'))
Qf=lambda t:L*t-t.square()/2
B=lambda t:L*L-L/2+L*t/2-L*S/(1-t)
fhead=L/2-L*S/(1-head).square()
phi0=2*B(head)/head-fhead
headslope=(fhead-phi0)/head

def lowF(t):
    """Primitive range, using only shape and the scalar cap constraints."""
    low=np.full(np.asarray(t.lo).shape,np.inf)
    high=np.full(np.asarray(t.hi).shape,-np.inf)
    for aa,bb,kind in [('0','.2635','head'),('.2635','.2918','prefix'),('.2918','.36','free'),('.36','.782','central')]:
        a=float(I(Q(aa)).lo);b=float(I(Q(bb)).hi)
        hit=(t.hi>=a)&(t.lo<=b)
        x=I(np.maximum(a,np.minimum(b,t.lo)),np.maximum(a,np.minimum(b,t.hi)))
        if kind=='head':v=phi0*x+headslope*x.square()/2;vlo,vhi=v.lo,v.hi
        elif kind=='prefix':v=B(x);vlo,vhi=v.lo,v.hi
        elif kind=='free':
            cc=I(Q('.2918'))
            ec=B(cc)-Qf(cc)+S
            sc=L-cc-(L/2-L*S/(1-cc).square())
            rem=ec-sc*(x-cc)
            floor=Qf(x)-S+I(np.maximum(0.,rem.lo),np.maximum(0.,rem.hi))
            vlo=floor.lo;vhi=B(x).hi
        else:v=Qf(x)-S;vlo,vhi=v.lo,v.hi
        low=np.where(hit,np.minimum(low,vlo),low)
        high=np.where(hit,np.maximum(high,vhi),high)
    assert np.all(np.isfinite(low)) and np.all(np.isfinite(high))
    return I(low,high)

r=I(Q('.34854'));a=r;b=r
A=L-a-I(Q('.00024'))-I(Q('.309'))*(rc-a)
Bs=L-b-I(Q('.00024'))-I(Q('.309'))*(rc-b)
dr=rc-r
R=Qf(r)-S+I(Q('.000000087'))+I(Q('.00024'))*dr+I(Q('.309'))*dr.square()/2
P=Qf(1-r)-S;h=2*L-a;k=r+b-L
D=h*R-k*P
C=(A*R+Bs*P)/D;alpha=(k*A+h*Bs)/D
m=C-1+alpha*r
assert min(D.lo,m.lo,alpha.lo)>0
assert ((C-1)*(I(Q('.775'))-L)+alpha*(Qf(I(Q('.775'))-r)-Qf(I(Q('.775'))))).hi<0
assert Q('.875')-Q('.65')+Q('.562330')<Q('.8')

def evaluate(box):
    global S,phi0,headslope,R,P,D,C,alpha,m,A,Bs
    S=I(box[:,6],box[:,7])
    fhead=L/2-L*S/(1-head).square()
    phi0=2*B(head)/head-fhead
    headslope=(fhead-phi0)/head
    R=Qf(r)-S+I(Q('.000000087'))+I(Q('.00024'))*dr+I(Q('.309'))*dr.square()/2
    P=Qf(1-r)-S
    D=h*R-k*P
    C=(A*R+Bs*P)/D;alpha=(k*A+h*Bs)/D
    m=C-1+alpha*r
    p,q,z=[I(box[:,2*j],box[:,2*j+1]) for j in range(3)]
    delay=I(np.maximum(0.,(z-p+q).lo),np.minimum(.8,(z-p+q).hi))
    dl=I(np.minimum(float(I(Q('.782')).hi),delay.lo),np.minimum(float(I(Q('.782')).hi),delay.hi))
    low=lowF(dl)
    dh=I(np.maximum(float(I(Q('.782')).lo),delay.lo),np.maximum(float(I(Q('.782')).lo),delay.hi))
    high=Qf(dh)-S
    up=np.where(delay.hi<=float(I(Q('.782')).lo),low.hi,
                np.where(delay.lo>=float(I(Q('.782')).hi),high.hi,np.maximum(low.hi,high.hi)))
    K0=I(np.zeros(up.shape),up)-lowF(q)-Qf(z)+S
    t=I(np.maximum(0.,(z-I(Q('.782'))).lo),np.maximum(0.,(z-I(Q('.782'))).hi))
    g0=(C-1)*(z-L)+alpha*(Qf(z-r)-Qf(z))
    gp=I(np.maximum(0.,g0.lo),np.maximum(0.,g0.hi))
    # Integrate E'>=g0+alpha E starting when affine g0 crosses zero.
    # The first two nonnegative terms of e_min suffice.
    ee=gp+alpha*gp.square()/(2*m)
    e=I(np.maximum(0.,ee.lo))
    qpl=Qf(I(p.hi));qph=Qf(I(p.lo))
    beta_min=p/(I(qpl.lo,qph.hi)-S)
    # Root ceiling integrated backwards from F(1)=0.
    beta_max=p/((1-p)*((1+p)/2-L))
    positive=(1-beta_max*t/2).lo>0
    KK=K0+t*e/2
    negative=KK.hi<0
    upper=q.hi-e.lo+beta_min.lo*KK.hi
    # Above arithmetic is scalar numpy, round each final operation upward.
    upper=(q-e+I(beta_min.lo)*I(KK.hi)).hi
    # On the free low segment, the strengthened primitive floor makes
    # this upper residual piecewise linear in q. Its maximum occurs at
    # an endpoint or where the remaining-area floor first becomes zero.
    cc=I(Q('.2918'))
    ec=B(cc)-Qf(cc)+S
    sc=L-cc-(L/2-L*S/(1-cc).square())
    kink=cc+ec/sc
    choices=[I(q.lo),I(q.hi),I(np.clip(kink.lo,q.lo,q.hi),np.clip(kink.hi,q.lo,q.hi))]
    qqmax=np.full(q.lo.shape,-np.inf)
    for qq in choices:
        rem=ec-sc*(qq-cc)
        rem=I(np.maximum(0.,rem.lo),np.maximum(0.,rem.hi))
        kval=p*(z-L-p/2)-(z-p)*qq-rem+S+t*e/2
        vv=qq-e+I(beta_min.lo)*kval
        qqmax=np.maximum(qqmax,vv.hi)
    eligible=(q.lo>=float(cc.hi))&(delay.lo>=float(I(Q('.36')).hi))
    upper=np.where(eligible,np.minimum(upper,qqmax),upper)
    return upper,positive&negative

def run():
    active=np.array([[float(I(Q('.65')).lo),float(I(Q('.875')).hi),0.,float(L.hi),float(I(Q('.65')).lo),float(I(Q('.875')).hi),float(I(Q('.02271790')).lo),float(I(Q('.023354')).hi)]])
    visited=leaves=0;worst=-np.inf;start=time.time();depth=0
    while len(active):
        active=active[active[:,5]>=active[:,0]]
        # The actual domain has z>=p, so narrow projected rank intervals.
        active[:,1]=np.minimum(active[:,1],active[:,5])
        active[:,4]=np.maximum(active[:,4],active[:,0])
        up,valid=evaluate(active);visited+=len(active);good=(up<0)&valid
        if np.any(good):worst=max(worst,float(np.max(up[good])))
        leaves+=int(np.sum(good));bad=active[~good]
        print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'upper':float(np.max(up)),'seconds':time.time()-start}),flush=True)
        if not len(bad):break
        if visited>10000000:raise RuntimeError('box budget exceeded')
        widths=bad[:,1::2]-bad[:,::2]
        which=np.argmax(widths*np.array([4.,2.,5.,200.]),axis=1)
        ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
        assert np.max(widths)>1e-9,'remaining intrinsic bound failure'
        left=bad.copy();right=bad.copy();left[ids,2*which+1]=mid;right[ids,2*which]=mid
        active=np.vstack([left,right]);depth+=1
    out={'status':'verified structural HC through z=.875 for p>=.65',
         'p_range':['.65','.875'],'z_range':['p','.875'],
         'q_range':['0','L'],'L_range':['.562325','.562330'],
         'S_range':['.02271790','.023354'],
         'cut_parameters':'computed interval-wise from each scalar S box',
         'visited':visited,'leaves':leaves,'strict_HC_upper':worst,
         'completion':'q>=L follows from high concavity; applies after the true join using cap preservation',
         'seconds':time.time()-start}
    Path(__file__).with_name('structural_large_hc_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':run()
