"""Validate an explicit low score against the selected independent-root family.

Work in progress: each reported status states which bounds were checked.
All profile coefficients come from the exact-corrected Reference constructor.
"""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path
import time
import numpy as np

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I, Reference, down, up


class Low:
    def __init__(self,ref):
        self.ref=ref
        self.L,self.S,self.c,self.rc=map(float,(ref.L,ref.S,ref.c,ref.rc))
        self.nodes=np.array([float(x) for x in ref.curvature_nodes])
        self.nodeI=I(np.array([float(I(p['lo']).lo) for p in ref.pieces]),
                     np.array([float(I(p['lo']).hi) for p in ref.pieces]))
        self.coeff={}
        for key in ('F','phi','dphi','ddphi'):
            rows=[]
            for p in ref.pieces:
                co=p['F'] if key=='F' else p['phi']
                for _ in range({'F':0,'phi':0,'dphi':1,'ddphi':2}[key]):
                    co=[F(i)*v for i,v in enumerate(co) if i]
                rows.append(co)
            self.coeff[key]=I(np.array([[float(I(v).lo) for v in row] for row in rows]),
                              np.array([[float(I(v).hi) for v in row] for row in rows]))

    def point(self,x,key):
        """Interval evaluation at exact binary64 x; piece choice is checked."""
        x=np.asarray(x,dtype=float)
        anslo=np.empty_like(x);anshi=np.empty_like(x)
        mask0=x<self.c;mask1=x>self.rc;mask=~(mask0|mask1)
        if np.any(mask0):
            X=I(x[mask0]);L,S=I(self.ref.L),I(self.ref.S)
            if key=='F': v=L*L-L/2+L*X/2-L*S/(1-X)
            elif key=='phi':v=L/2-L*S/(1-X).square()
            elif key=='dphi':v=-2*L*S/((1-X).square()*(1-X))
            else:v=-6*L*S/((1-X).square().square())
            anslo[mask0]=v.lo;anshi[mask0]=v.hi
        if np.any(mask1):
            X=I(x[mask1]);L,S=I(self.ref.L),I(self.ref.S)
            if key=='F':v=L*X-X.square()/2-S
            elif key=='phi':v=L-X
            elif key=='dphi':v=I(-np.ones_like(X.lo))
            else:v=I(np.zeros_like(X.lo))
            anslo[mask1]=v.lo;anshi[mask1]=v.hi
        if np.any(mask):
            xx=x[mask];idx=np.minimum(np.searchsorted(self.nodes,xx,side='right')-1,len(self.nodes)-2)
            idx=np.maximum(idx,0)
            # Binary64 knots need not equal the rational knots. Evaluate both
            # neighboring polynomials in the tiny ambiguous endpoint sliver;
            # all profile values/first derivatives agree at internal knots.
            co=self.coeff[key]
            dx=I(xx)-I(self.nodeI.lo[idx],self.nodeI.hi[idx])
            value=I(co.lo[idx,-1],co.hi[idx,-1])
            for j in range(co.lo.shape[1]-2,-1,-1):
                value=value*dx+I(co.lo[idx,j],co.hi[idx,j])
            # At a rounded internal rational knot the search index may be
            # one piece to either side. Take both polynomial extensions;
            # one is necessarily the actual value.
            for shift in (-1,1):
                jj=np.clip(idx+shift,0,len(self.nodes)-2)
                edge=np.where(shift<0,self.nodes[idx],self.nodes[idx+1])
                amb=(xx==edge)&(jj!=idx)
                if np.any(amb):
                    di=I(xx[amb])-I(self.nodeI.lo[jj[amb]],self.nodeI.hi[jj[amb]])
                    vv=I(co.lo[jj[amb],-1],co.hi[jj[amb],-1])
                    for k in range(co.lo.shape[1]-2,-1,-1):
                        vv=vv*di+I(co.lo[jj[amb],k],co.hi[jj[amb],k])
                    value.lo[amb]=np.minimum(value.lo[amb],vv.lo)
                    value.hi[amb]=np.maximum(value.hi[amb],vv.hi)
            anslo[mask]=value.lo;anshi[mask]=value.hi
        # The exact c and rc may be between adjacent binary64 numbers.
        # Include both formulas at every binary endpoint of those slivers.
        for endpoint,prefix in [(self.ref.c,True),(self.ref.rc,False)]:
            ep=I(endpoint);amb=(x>=ep.lo)&(x<=ep.hi)
            if not np.any(amb):continue
            X=I(x[amb]);L,S=I(self.ref.L),I(self.ref.S)
            if prefix:
                if key=='F':v=L*L-L/2+L*X/2-L*S/(1-X)
                elif key=='phi':v=L/2-L*S/(1-X).square()
                elif key=='dphi':v=-2*L*S/((1-X).square()*(1-X))
                else:v=-6*L*S/(1-X).square().square()
                pp=0
            else:
                if key=='F':v=L*X-X.square()/2-S
                elif key=='phi':v=L-X
                elif key=='dphi':v=I(-np.ones_like(X.lo))
                else:v=I(np.zeros_like(X.lo))
                pp=len(self.nodes)-2
            co=self.coeff[key];dx=X-I(self.ref.pieces[pp]['lo'])
            vv=I(co.lo[pp,-1],co.hi[pp,-1])
            for k in range(co.lo.shape[1]-2,-1,-1):
                vv=vv*dx+I(co.lo[pp,k],co.hi[pp,k])
            anslo[amb]=np.minimum(anslo[amb],np.minimum(v.lo,vv.lo))
            anshi[amb]=np.maximum(anshi[amb],np.maximum(v.hi,vv.hi))
        return I(anslo,anshi)

    def floating(self,x,key):
        v=self.point(x,key)
        return (v.lo+v.hi)/2

    def interval(self,lo,hi,key):
        # F increases, phi and dphi decrease throughout each smooth low block.
        p=self.point(lo,key);q=self.point(hi,key)
        if key=='F':return I(p.lo,q.hi)
        if key in ('phi','dphi'):return I(q.lo,p.hi)
        raise ValueError(key)


def qval(L,x):return L*x-x.square()/2


def semiconcavity_bound(ref,rmin,rmax):
    """Coarse exact quotient bound, valid on each smooth layer phase."""
    for p in ref.pieces:
        length=p['hi']-p['lo'];co=p['phi']
        curv=[-2*co[2],-2*co[2]-6*co[3]*length]
        slope=[co[1],co[1]+2*co[2]*length+3*co[3]*length**2]
        assert min(curv)>0 and max(curv)<F('10.1')
        assert min(slope)>-1 and max(slope)<F('-.1')
    # R and P bounds may be deliberately wider than this reference needs.
    U=F('.313');A=B=F('.27');R=F('.136');P=F('.134')
    K=F('.111');h=F('.84')
    Kr=max(abs(F('.775')-ref.L-rmax),abs(F('.875')-ref.L-rmin))
    k=max(abs(2*rmax-ref.L),abs(rmin+ref.c-ref.L))
    Pp=1-rmin-ref.L
    d=F('.0527');curv=F('10.1')
    G=k*A+h*B
    M=U*(A*R+B*P)+K*G
    Mp=U*(A*B+P+B*Pp)+Kr*G+K*(2*A+h)
    Mpp=U*(A+curv*P+2*Pp+B)+G+2*Kr*(2*A+h)+K*h*curv
    Dp=h*B+2*P+k*Pp;Dpp=h+4*Pp+k
    bound=Mpp/d+2*Mp*Dp/d**2+M*Dpp/d**2+2*M*Dp**2/d**3
    assert bound<1000
    return bound


def coefficients(ref,step,rmin,rmax):
    low=Low(ref);L,S=I(ref.L),I(ref.S)
    assert F('.25')<=rmin<=ref.c<ref.rc<=rmax<=F('.36')
    n=int(round(float(rmax-rmin)/step))
    grid=[rmin+(rmax-rmin)*F(i,n) for i in range(n+1)]
    grid=sorted(set(grid+[ref.c,ref.rc]))
    ri=I(np.array([float(I(x).lo) for x in grid]),np.array([float(I(x).hi) for x in grid]))
    rr=(ri.lo+ri.hi)/2
    R=low.interval(ri.lo,ri.hi,'F');P=qval(L,1-ri)-S
    Br=low.interval(ri.lo,ri.hi,'phi')
    Rf=(R.lo+R.hi)/2;Pf=(P.lo+P.hi)/2;Bf=(Br.lo+Br.hi)/2
    # f(a)=AR+BP+phi'(a)D is strictly decreasing, including a=r.
    def fun(a):
        A=low.floating(a,'phi');dp=low.floating(a,'dphi')
        dp=np.where(a==low.c,float(ref.pieces[0]['phi'][1]),dp)
        pend=ref.pieces[-1];dl=pend['hi']-pend['lo'];co=pend['phi']
        dp=np.where(a==low.rc,float(co[1]+2*co[2]*dl+3*co[3]*dl**2),dp)
        b=np.maximum(a,rr);B=np.where(a>=rr,A,Bf)
        D=(2*low.L-a)*Rf-(rr+b-low.L)*Pf
        return A*Rf+B*Pf+dp*D
    lo=np.full_like(rr,low.c);hi=np.full_like(rr,low.rc)
    fc=fun(lo);frc=fun(hi)
    pin=fc<=0;pinright=frc>=0
    for _ in range(47):
        mid=(lo+hi)/2;fm=fun(mid)
        lo=np.where(fm>0,mid,lo);hi=np.where(fm>0,hi,mid)
    a=(lo+hi)/2
    # An exact reference endpoint is handled as a singleton interval below.
    al=np.maximum(low.c,a-2e-12);ah=np.minimum(low.rc,a+2e-12)
    al[pin]=float(I(ref.c).lo);ah[pin]=float(I(ref.c).hi)
    al[pinright]=float(I(ref.rc).lo);ah[pinright]=float(I(ref.rc).hi)
    ai=I(al,ah);A=low.interval(al,ah,'phi')
    early=al>=ri.hi;late=ah<=ri.lo
    # Coinciding a/r is enclosed by the hull of the two score choices.
    B=I(np.where(early,A.lo,np.where(late,Br.lo,np.minimum(A.lo,Br.lo))),
        np.where(early,A.hi,np.where(late,Br.hi,np.maximum(A.hi,Br.hi))))
    bi=I(np.maximum(ai.lo,ri.lo),np.maximum(ai.hi,ri.hi))
    h=2*L-ai;k=ri+bi-L;D=h*R-k*P
    assert np.all(D.lo>0)
    C=(A*R+B*P)/D;alpha=(k*A+h*B)/D
    def fi(ap,side):
        aa=I(ap);AA=low.point(ap,'phi');dA=low.point(ap,'dphi')
        # c uses its free-arc RIGHT derivative, not prefix derivative.
        if side=='left':
            mask=pin
            dp0=I(ref.pieces[0]['phi'][1])
            dA=I(np.where(mask,float(dp0.lo),dA.lo),np.where(mask,float(dp0.hi),dA.hi))
        bb=I(np.maximum(ap,ri.lo),np.maximum(ap,ri.hi))
        BB=I(np.where(ap>=ri.hi,AA.lo,np.where(ap<=ri.lo,Br.lo,np.minimum(AA.lo,Br.lo))),
             np.where(ap>=ri.hi,AA.hi,np.where(ap<=ri.lo,Br.hi,np.maximum(AA.hi,Br.hi))))
        DD=(2*L-aa)*R-(ri+bb-L)*P
        return AA*R+BB*P+dA*DD
    fl=fi(al,'left');fh=fi(ah,'right')
    if np.any(pin):
        aa=I(ref.c);AA=I(ref.L/2-ref.L*ref.S/(1-ref.c)**2)
        dA=I(ref.pieces[0]['phi'][1]);bb=I(np.maximum(float(aa.lo),ri.lo),np.maximum(float(aa.hi),ri.hi))
        BB=I(np.where(ri.hi<=aa.lo,float(AA.lo),Br.lo),np.where(ri.hi<=aa.lo,float(AA.hi),Br.hi))
        exactfc=AA*R+BB*P+dA*((2*L-aa)*R-(ri+bb-L)*P)
        fl=I(np.where(pin,exactfc.lo,fl.lo),np.where(pin,exactfc.hi,fl.hi))
    # All nonpinned roots are enclosed by certified sign-changing brackets.
    assert np.all(fl.lo[~pin&~pinright]>0),(np.min(fl.lo[~pin&~pinright]),'left root bracket')
    assert np.all(fh.hi[~pin&~pinright]<0),(np.max(fh.hi[~pin&~pinright]),'right root bracket')
    assert np.all(fl.hi[pin]<0),(np.max(fl.hi[pin]),'c pin')
    assert not np.any(pinright),'right pinned roots need separate endpoint check'
    # The cap prefix has much shallower score slope; the central continuation
    # has slope -1. Thus these roots maximize support on the entire root box.
    assert np.min(C.lo)>F('.1') and np.max(C.hi)<1
    # Conservative rational coefficient endpoints; these define the new ODE.
    Cu=up(C.hi);au=up(alpha.hi)
    gaps=np.diff([float(x) for x in grid]);maxgap=max(grid[i+1]-grid[i] for i in range(len(grid)-1))
    return {'r':ri,'C':I(Cu),'alpha':I(au),'maxgap':maxgap,
            'a':ai,'D':D,'rawC':C,'rawalpha':alpha,'pin':pin,
            'low':low,'grid':grid}


def low_checks(ref,data,rmin,rmax):
    low=data['low'];L,S=I(ref.L),I(ref.S)
    # Cell boxes cover all layer ranks, not just the coefficient nodes.
    rr=I(data['r'].lo[:-1],data['r'].hi[1:])
    R=low.interval(rr.lo,rr.hi,'F');P=qval(L,1-rr)-S
    assert np.all(R.lo>F('.085')) and np.all(R.hi<F('.136'))
    assert np.all(P.lo>0) and np.all(P.hi<F('.134'))
    assert np.all((L*R-rr*P).lo>0),'opposite binary'
    # D decreases in each independent root rank; the broad root box ends .38.
    D=(2*L-I(F('.38')))*R-(rr+I(F('.38'))-L)*P
    assert np.all(D.lo>F('.0527'))
    # At a=rc the scalar root function is negative throughout the layer box.
    a=I(ref.rc);A=L-a
    co=ref.pieces[-1]['phi'];length=ref.pieces[-1]['hi']-ref.pieces[-1]['lo']
    dp=I(co[1]+2*co[2]*length+3*co[3]*length**2)
    Br=low.interval(rr.lo,rr.hi,'phi');B=I(np.where(rr.hi<=a.lo,float(A.lo),Br.lo),np.where(rr.lo>=a.hi,Br.hi,float(A.hi)))
    b=I(np.maximum(rr.lo,float(a.lo)),np.maximum(rr.hi,float(a.hi)))
    f=A*R+B*P+dp*((2*L-a)*R-(rr+b-L)*P)
    assert np.all(f.hi<0),'all roots below rc'
    assert float(low.point(np.array([float(ref.c)]),'phi').hi[0])<.27
    assert ref.L/2-ref.L*ref.S/(1-rmin)**2<F('.27')
    # Rational-prefix ceiling and shallow slope, proved by monotonic endpoint
    # formulas. The free score has slopes in (-1,-.1) and joins the ceiling
    # at rc, so it lies below the ceiling and below the cap score after c.
    assert ref.L/2-ref.c+ref.L*ref.S/(1-ref.c)**2>0
    assert 2*ref.L*ref.S/(1-ref.c)**3<F('.1')
    assert 2*ref.L*ref.S/(1-F('.385'))**3<F('.12')
    # On [c,rc] the free slope is below -.7; the cap slope derivative is
    # above -.12, so primitive contact at c is followed by strict cap slack.
    assert ref.pieces[0]['phi'][1]<F('-.7')
    # On [rc,.385], the ceiling score is already below the cap score and
    # falls faster, preserving the primitive cap through the class endpoint.
    assert ref.L-ref.rc < ref.L/2-ref.L*ref.S/(1-ref.rc)**2
    # Every reduced root has score at least L-.35, while its determinant is
    # at most .84*.136+.14*.134. Hence C>.1 uniformly, not merely at nodes.
    assert (ref.L-rmax)*(F('.085')+F('.115'))/(F('.84')*F('.136')+F('.16')*F('.134'))>F('.1')
    assert np.all(P.lo>F('.115'))
    # K is positive under the high root ceiling and below .111 under the
    # lower root budget; these bounds also ensure c_A,c_B>0 for every root.
    Umin=F('.775')-ref.L;Umax=F('.875')-ref.L
    assert min(r*Umin-r*r/2 for r in [rmin,rmax])>0
    assert Umax**2/2+ref.L-F('.5')-ref.S<F('.111')
    assert Umin*F('.085')+(rmin+F('.285')-ref.L)*F('.111')>0
    # Global terminal interpolation: |B_qq|<1000 and |B_zz|<1000-2.
    d=F('.282');z=F('.875');N=F('.2');Nq=F('.6');Nqq=F('1.2')
    Q=lambda x:ref.L*x-x*x/2
    assert Q(F('.385'))-ref.S-ref.rat_F(F('.28'))>0
    assert ref.L**2/2<N
    assert F(0)<ref.L-F(1)+F('.775')-F('.28')
    assert ref.L-F(1)+F('.875')-F('.26')<F('.3')
    assert ref.L/2<F('.3')
    assert 2*ref.L*ref.S/(1-F('.28'))**3<F('.2')
    terminal_q2=z*(Nqq/d+2*Nq/d**2+2*N/d**3)
    terminal_z2=(2*F('.3')+z)/d
    assert terminal_q2<1000 and terminal_z2<998
    return {'opposite_binary_margin':float(np.min((L*R-rr*P).lo)),
            'full_root_determinant_lower':float(np.min(D.lo)),
            'terminal_q_second_bound':str(terminal_q2),'terminal_z_second_bound':str(terminal_z2)}


def run(path,rstep,zstep,qstep,rmin=F('.26'),rmax=F('.35')):
    start=time.time();ref=Reference(path)
    data=coefficients(ref,rstep,rmin,rmax)
    checks=low_checks(ref,data,rmin,rmax)
    bound=semiconcavity_bound(ref,rmin,rmax)
    out={'status':'selected-family numerical/interval flow in progress',
         'reference':path,'L':str(ref.L),'S':str(ref.S),
         'layer_interval':[str(rmin),str(rmax)],
         'layer_nodes':len(data['grid']),'a_range':data['a'].bounds(),
         'C_range':data['rawC'].bounds(),'alpha_range':data['rawalpha'].bounds(),
         'D_range':data['D'].bounds(),'pinned_left_nodes':int(np.sum(data['pin'])),
         'root_coefficient_width':float(np.max(data['rawC'].hi-data['rawC'].lo)),
         'layer_semiconcavity_bound':str(bound),'low_checks':checks,'seconds':time.time()-start}
    print(json.dumps(out,indent=2),flush=True)
    L,S=I(ref.L),I(ref.S);r=data['r'];C=data['C'];alpha=data['alpha']
    # Each coefficient is an exact binary rational, chosen above its proved
    # true value. U,K>0 make both replacements conservative lower caps.
    penalty=I(F(1000)*data['maxgap']**2/8)
    n=int(round(.1/zstep));step=F('.1')/n;dt=I(step)
    z0=F('.775');Y=qval(L,I(z0))-S
    nqs=int(round(.02/qstep));qgrid=[F('.26')+F('.02')*F(i,nqs) for i in range(nqs+1)]
    q=I(np.array([float(I(x).lo) for x in qgrid]),np.array([float(I(x).hi) for x in qgrid]))
    Fq=L*L-L/2+L*q/2-L*S/(1-q)
    qpenalty=I(F(1000)*(F('.02')/nqs)**2/8)
    zpenalty=I(F(1000)*step**2/8)
    def barrier(z):
        return z*(qval(L,1-z+q)-S-Fq)/(L-q)
    def cap(z,y):
        vals=-C*(z-L)+alpha*(y-qval(L,z-r)+S)-penalty
        root=L-z
        return I(min(float(root.lo),float(np.min(vals.lo))),
                 min(float(root.hi),float(np.min(vals.hi)))),vals
    minmargin=np.inf;minroot=np.inf;where=None;maxwidth=0.;maxactive=0
    Yhistory=[]
    global_second=0.
    for j in range(n+1):
        z=I(z0+j*step)
        b=barrier(z)
        margin=float((Y-I(float(np.max(b.hi)))-qpenalty-zpenalty).lo)
        rootmargin=float((Y-(qval(L,z)-qval(L,I(1)))-zpenalty).lo)
        if margin<minmargin:minmargin=margin;where=float(z.lo)
        minroot=min(minroot,rootmargin)
        maxwidth=max(maxwidth,float(Y.hi-Y.lo))
        if j==n:break
        Gleft,_=cap(z,Y)
        zcell=I(float(z.lo),float(I(z0+(j+1)*step).hi))
        # Root and moving slopes remain in [-1,0] in this state box. The
        # first enclosure can be made looser without affecting Taylor order.
        Ycell=I(float((Y-dt).lo),float(Y.hi))
        Gcell,vals=cap(zcell,Ycell)
        assert float(Gcell.lo)>-1 and float(Gcell.hi)<0
        active=vals.lo<=float(Gcell.hi)
        roots_possible=float((L-zcell).lo)<=float(Gcell.hi)
        maxactive=max(maxactive,int(np.sum(active)))
        beta_prime=-I(C.lo[active],C.hi[active])-I(alpha.lo[active],alpha.hi[active])*(L-zcell+I(r.lo[active],r.hi[active]))
        sec=I(alpha.lo[active],alpha.hi[active])*Gcell+beta_prime
        slo=float(np.min(sec.lo)) if np.any(active) else np.inf
        shi=float(np.max(sec.hi)) if np.any(active) else -np.inf
        if roots_possible:slo=min(slo,-1.);shi=max(shi,-1.)
        assert np.isfinite(slo) and np.isfinite(shi)
        global_second=max(global_second,abs(slo),abs(shi))
        Y=Y+dt*Gleft+dt.square()/2*I(slo,shi)
        # All selected moving controls stay in their certified high budget
        # domain if this maintained lower root budget holds.
        assert float(Y.lo)>float((qval(L,I(z0+(j+1)*step))-qval(L,I(1))).hi)
        if j%1000==0:
            Yhistory.append([float(I(z0+(j+1)*step).lo),float(Y.lo),float(Y.hi),minmargin])
            print('flow',j,n,'width',maxwidth,'margin',minmargin,flush=True)
    assert global_second<2
    assert minmargin>0 and minroot>0
    out.update({'status':'selected independent-root family feasible, subject to companion proof audit; not an all-election upper certificate',
                'z_steps':n,'q_nodes':len(qgrid),'layer_penalty':penalty.bounds(),
                'q_penalty':qpenalty.bounds(),'z_penalty':zpenalty.bounds(),
                'terminal_binary_margin_lower':minmargin,'minimum_margin_z':where,
                'root_budget_margin_lower':minroot,'maximum_flow_width':maxwidth,
                'maximum_active_layer_nodes':maxactive,'maximum_high_second_derivative':global_second,
                'Yterminal':Y.bounds(),'flow_samples':Yhistory,'seconds':time.time()-start})
    print(json.dumps(out,indent=2),flush=True)
    return out


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--reference',default='research/closure/root/warped_cubic_ordered_reference_242.json')
    p.add_argument('--rstep',type=float,default=1e-5)
    p.add_argument('--zstep',type=float,default=1e-5)
    p.add_argument('--qstep',type=float,default=1e-5)
    p.add_argument('--rmin',default='.26')
    p.add_argument('--rmax',default='.35')
    p.add_argument('--output',default='research/closure/root/selected_family_feasibility_242.json')
    a=p.parse_args();out=run(a.reference,a.rstep,a.zstep,a.qstep,F(a.rmin),F(a.rmax))
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
