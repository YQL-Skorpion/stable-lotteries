"""Outward-rounded interval certificate for an explicit warped reference.

All decimal reference inputs are exact rationals. Polynomial reference ranges
are enclosed with Fraction arithmetic; remaining arithmetic uses IEEE binary64
operations enlarged by nextafter after every operation. exp is enclosed by a
Taylor series with an explicit positive remainder. No sampled Hessian is used.

This certifies coefficient bounds for the stored piecewise-linear controls,
not an exact optimizer or a full VI. Coverage gaps, if present, are reported
explicitly. The extended reference supplies both previously missing segments.
"""
import argparse
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path
import time
import numpy as np


def down(x):
    return np.nextafter(x, -np.inf)


def up(x):
    return np.nextafter(x, np.inf)


class I:
    def __init__(self, lo, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, F):
            x = float(lo)
            self.lo = np.array(x if F(x) <= lo else np.nextafter(x, -np.inf))
            self.hi = np.array(x if F(x) >= lo else np.nextafter(x, np.inf))
        else:
            self.lo = np.asarray(lo, dtype=float)
            self.hi = np.asarray(lo if hi is None else hi, dtype=float)

    def __add__(self, other):
        if isinstance(other, J):
            return NotImplemented
        other = I(other)
        return I(down(self.lo + other.lo), up(self.hi + other.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        if isinstance(other, J):
            return NotImplemented
        return self + (-I(other))

    def __rsub__(self, other):
        return I(other) + (-self)

    def __mul__(self, other):
        if isinstance(other, J):
            return NotImplemented
        other = I(other)
        products = np.stack(np.broadcast_arrays(
            self.lo * other.lo, self.lo * other.hi,
            self.hi * other.lo, self.hi * other.hi))
        return I(down(np.min(products, axis=0)), up(np.max(products, axis=0)))

    __rmul__ = __mul__

    def reciprocal(self):
        assert np.all((self.lo > 0) | (self.hi < 0)), ('zero divisor', self.lo.min(), self.hi.max())
        return I(down(1 / self.hi), up(1 / self.lo))

    def __truediv__(self, other):
        if isinstance(other, J):
            return NotImplemented
        return self * I(other).reciprocal()

    def __rtruediv__(self, other):
        return I(other) * self.reciprocal()

    def square(self):
        lo = np.minimum(self.lo * self.lo, self.hi * self.hi)
        lo = np.where((self.lo <= 0) & (self.hi >= 0), 0., down(lo))
        return I(lo, up(np.maximum(self.lo * self.lo, self.hi * self.hi)))

    def sqrt(self):
        assert np.all(self.lo >= 0), ('negative square root', self.lo.min())
        return I(np.maximum(0., down(np.sqrt(self.lo))), up(np.sqrt(self.hi)))

    def axis(self, count=1):
        tail = (None,) * count
        return I(self.lo[(...,) + tail], self.hi[(...,) + tail])

    def take(self, *indices):
        return I(self.lo[(...,) + indices], self.hi[(...,) + indices])

    def bounds(self):
        return [float(np.min(self.lo)), float(np.max(self.hi))]


def outer(a, b):
    return I(a.lo[..., :, None], a.hi[..., :, None]) * I(b.lo[..., None, :], b.hi[..., None, :])


class J:
    """Interval value, gradient and Hessian in (S,r,a)."""
    def __init__(self, v, g=None, h=None):
        self.v = I(v)
        self.g = I(np.zeros(self.v.lo.shape + (3,))) if g is None else g
        self.h = I(np.zeros(self.v.lo.shape + (3, 3))) if h is None else h

    @staticmethod
    def var(value, index):
        ans = J(value)
        ans.g.lo[..., index] = 1
        ans.g.hi[..., index] = 1
        return ans

    def __add__(self, other):
        other = other if isinstance(other, J) else J(other)
        return J(self.v + other.v, self.g + other.g, self.h + other.h)

    __radd__ = __add__

    def __neg__(self):
        return J(-self.v, -self.g, -self.h)

    def __sub__(self, other):
        return self + (-other if isinstance(other, J) else -I(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, J) else J(other)
        return J(self.v * other.v,
                 self.g * other.v.axis() + other.g * self.v.axis(),
                 self.h * other.v.axis(2) + other.h * self.v.axis(2)
                 + outer(self.g, other.g) + outer(other.g, self.g))

    __rmul__ = __mul__

    def loghess(self):
        assert np.all(self.v.lo > 0), ('nonpositive logarithm', self.v.lo.min())
        return self.h / self.v.axis(2) - outer(self.g, self.g) / self.v.square().axis(2)


def exp_positive(x):
    """Taylor enclosure, valid for 0<=x<1; no libm exponential."""
    x = I(x)
    assert np.all(x.lo >= 0) and np.all(x.hi < 1)
    term = I(1.)
    ans = term
    for k in range(1, 19):
        term = term * x / I(k)
        ans = ans + term
    nextterm = term * x / I(19)
    remainder = nextterm / (I(1.) - x / I(20))
    return I(ans.lo, up(ans.hi + remainder.hi))


def rational(value):
    return F(str(value))


def exact_poly_value(coeff, x):
    ans = F(0)
    for c in reversed(coeff):
        ans = ans * x + c
    return ans


def exact_poly_range(coeff, lo, hi):
    """Centered-power enclosure of a rational polynomial."""
    center, radius = (lo + hi) / 2, (hi - lo) / 2
    shifted = [sum((coeff[k] * comb(k, j) * center ** (k-j)
                    for k in range(j, len(coeff))), F(0)) * radius ** j
               for j in range(len(coeff))]
    error = sum((abs(c) for c in shifted[1:]), F(0))
    return I(shifted[0] - error).lo.item(), I(shifted[0] + error).hi.item()


class Reference:
    def __init__(self, path):
        self.raw = json.load(open(path))
        self.L, self.S, self.c, self.rc = [rational(self.raw[k]) for k in ['L', 'Sstar', 'c', 'rc']]
        self.phi = [rational(x) for x in self.raw.get('phi_power_coefficients', [])]
        self.du = [rational(x) for x in self.raw['u_prime_power_coefficients']]
        self.h = self.rc - self.c
        # Make the explicit low reference exactly continuous at both joins
        # and give it exactly the prescribed central area.
        target0=self.L/2-self.L*self.S/(1-self.c)**2
        target1=self.L-self.rc
        targetI=(self.L*self.rc-self.rc*self.rc/2-self.S-self.rat_F(self.c))/self.h
        self.curvature_nodes=[]
        if 'curvature_nodes' in self.raw:
            self.curvature_nodes=[rational(x) for x in self.raw['curvature_nodes']]
            if 'curvature_pairs' in self.raw:
                pairs=[tuple(rational(v) for v in x) for x in self.raw['curvature_pairs']]
            else:pairs=[(rational(x),rational(x)) for x in self.raw['curvature_values']]
            assert self.curvature_nodes[0]==self.c and self.curvature_nodes[-1]==self.rc
            assert len(pairs)+1==len(self.curvature_nodes)
            xx=[x-self.c for x in self.curvature_nodes]
            lengths=[b-a for a,b in zip(xx,xx[1:])]
            assert all(x>0 for x in lengths) and all(min(x)>0 for x in pairs)
            i1=[];weights=[]
            for left,length,(k0,k1) in zip(xx,lengths,pairs):
                dk=(k1-k0)/length
                i1.append(k0*((self.h-left)*length-length**2/2)+dk*((self.h-left)*length**2/2-length**3/3))
                constant=left*(self.h-left)
                weights.append(k0*(constant*length+(self.h-2*left)*length**2/2-length**3/3)
                               +dk*(constant*length**2/2+(self.h-2*left)*length**3/3-length**4/4))
            moment=2*self.h*(targetI-(target0+target1)/2)
            scale=moment/sum(weights,F(0))
            assert scale>0
            pairs=[(k0*scale,k1*scale) for k0,k1 in pairs]
            slope=(target1-target0+scale*sum(i1,F(0)))/self.h
            val,primitive=target0,self.rat_F(self.c)
            self.pieces=[]
            for node,length,(k,k1) in zip(self.curvature_nodes,lengths,pairs):
                dk=(k1-k)/length
                self.pieces.append({'lo':node,'hi':node+length,
                                    'phi':[val,slope,-k/2,-dk/6],
                                    'F':[primitive,val,slope/2,-k/6,-dk/24]})
                primitive+=val*length+slope*length**2/2-k*length**3/6-dk*length**4/24
                val+=slope*length-k*length**2/2-dk*length**3/6
                slope-=k*length+dk*length**2/2
            assert val==target1 and primitive==self.L*self.rc-self.rc**2/2-self.S
            self.curvature_correction=str(scale)
        else:
            e0=target0-self.phi[0];e1=target1-sum(self.phi)
            ei=targetI-sum((x/F(k+1) for k,x in enumerate(self.phi)),F(0))
            aa=e0;cc=3*(e0+e1-2*ei);bb=e1-e0-cc
            self.phi[0]+=aa;self.phi[1]+=bb;self.phi[2]+=cc
        # Correct the three tiny decimal endpoint/moment residuals exactly.
        desired0 = -self.L / (1-self.c)**2
        desiredI = (-1 + self.L/(1-self.c)) / self.h
        e0 = desired0 - self.du[0]
        e1 = -sum(self.du)
        ei = desiredI - sum((x/F(k+1) for k, x in enumerate(self.du)), F(0))
        # Add A+B w+C w^2 with prescribed endpoint values and integral.
        aa=e0; cc=3*(e0+e1-2*ei); bb=e1-e0-cc
        self.du[0]+=aa; self.du[1]+=bb; self.du[2]+=cc
        self.uint=[-self.L/(1-self.c)] + [self.h*x/F(k+1) for k,x in enumerate(self.du)]
        self.Fint=[self.rat_F(self.c)] + [self.h*x/F(k+1) for k,x in enumerate(self.phi)]

    def rat_F(self, x):
        return self.L*self.L-self.L/2+self.L*x/2-self.L*self.S/(1-x)

    def terminal_box(self):
        """Check membership in verify_terminal_warp.py's 650 certificate box."""
        if 'terminal_q' not in self.raw:
            return {'verified':False,'reason':'reference has no terminal_q'}
        q=rational(self.raw['terminal_q'])
        zend=rational(self.raw['controls'][-1]['z'])
        checks=[F('.562325')<=self.L<=F('.56233'),
                F('.2700')<=q<=F('.2703'),
                F('.8622')<=zend<=F('.8626'),
                F('.0230')<=self.S<=F('.0231'),
                F('.0219728')<=F('.02197280467819'),
                F('.026650314880436')<=F('.0266504')]
        return {'verified':all(checks),'curvature':650,'M0':'0.135',
                'companion_verifier':'research/closure/global/verify_terminal_warp.py',
                'companion_arguments':['--constant-m0','.135','--curvature','650'],
                'terminal_q':str(q),'terminal_z':str(zend)}

    def gauge_floor(self):
        answer=np.inf
        for k in range(64):
            data=self.ranges(self.c+self.h*F(k,64),self.c+self.h*F(k+1,64))
            ss=I(I(F('.02197280467819')).lo,I(F('.026650314880436')).hi)
            val=data['phi']+(ss-I(self.S))*data['du']
            answer=min(answer,float(val.lo))
        assert answer>0
        return answer

    def ranges(self, lo, hi):
        assert not (lo < self.c < hi), 'split control cell at prefix endpoint'
        if hi <= self.c and lo < self.c:
            vals=[self.L/2-self.L*self.S/(1-x)**2 for x in (hi,lo)]
            return {'F':I(I(self.rat_F(lo)).lo,I(self.rat_F(hi)).hi),
                    'phi':I(I(vals[0]).lo,I(vals[1]).hi),
                    'dphi':I(I(-2*self.L*self.S/(1-hi)**3).lo,I(-2*self.L*self.S/(1-lo)**3).hi),
                    'ddphi':I(I(-6*self.L*self.S/(1-hi)**4).lo,I(-6*self.L*self.S/(1-lo)**4).hi),
                    'u':I(I(-self.L/(1-hi)).lo,I(-self.L/(1-lo)).hi),
                    'du':I(I(-self.L/(1-hi)**2).lo,I(-self.L/(1-lo)**2).hi)}
        wlo,whi=(lo-self.c)/self.h,(hi-self.c)/self.h
        ans={}
        pairs=[('u',self.uint),('du',self.du)]
        if not self.curvature_nodes:
            dp=[F(i)*v/self.h for i,v in enumerate(self.phi) if i]
            ddp=[F(i)*v/self.h for i,v in enumerate(dp) if i]
            pairs+=[('F',self.Fint),('phi',self.phi),('dphi',dp),('ddphi',ddp)]
        for key,coeff in pairs:
            ans[key]=I(*exact_poly_range(coeff,wlo,whi))
        if self.curvature_nodes:
            for key in ('F','phi','dphi','ddphi'):
                boxes=[]
                for p in self.pieces:
                    if lo>p['hi'] or hi<p['lo']:continue
                    coeff=p[key] if key in ('F','phi') else [F(i)*v for i,v in enumerate(p['phi']) if i]
                    if key=='ddphi':coeff=[F(i)*v for i,v in enumerate(coeff) if i]
                    boxes.append(exact_poly_range(coeff,max(lo,p['lo'])-p['lo'],min(hi,p['hi'])-p['lo']))
                assert boxes
                ans[key]=I(min(x[0] for x in boxes),max(x[1] for x in boxes))
        assert ans['phi'].lo>0
        return ans


def split_cells(ref, subdivisions):
    nodes=[{k:rational(row[k]) for k in ('z','r','a')} for row in ref.raw['controls']]
    cells=[]
    for left,right in zip(nodes,nodes[1:]):
        points={F(k,subdivisions) for k in range(subdivisions+1)}
        for key in ('r','a'):
            for knot in [ref.c]+ref.curvature_nodes:
                if left[key] < knot < right[key]:
                    points.add((knot-left[key])/(right[key]-left[key]))
        dl,dr=left['a']-left['r'],right['a']-right['r']
        if dl*dr<0:
            points.add(-dl/(dr-dl))
        pts=sorted(points)
        def at(t):return {k:left[k]+t*(right[k]-left[k]) for k in left}
        for ta,tb in zip(pts,pts[1:]):
            a,b=at(ta),at(tb)
            cells.append({'left':a,'right':b,'dz':b['z']-a['z'],
                          'branch':'early' if a['a']+b['a']>=a['r']+b['r'] else 'late',
                          'rdata':ref.ranges(a['r'],b['r']),
                          'adata':ref.ranges(a['a'],b['a'])})
    return cells


def numerators(L, M0, branch, S, r, a, R, z):
    P=(1-r)*L-(1-r)*(1-r)*I(F(1,2))-S
    U=z-L; h=2*L-a; K=(z-r)*L-(z-r)*(z-r)*I(F(1,2))-M0
    k=r+a-L if branch=='early' else 2*r-L
    D=h*R-k*P
    if branch=='early':
        return D,[L+r,U*(R+P)+(L+r)*K]
    return D,[h,k,U*P+h*K,U*R+k*K]


def one_jet(value,first=0,second=0):
    first,second=I(first),I(second)
    gg=I(np.zeros(3),np.zeros(3));hh=I(np.zeros((3,3)),np.zeros((3,3)))
    gg.lo[0]=first.lo;gg.hi[0]=first.hi
    hh.lo[0,0]=second.lo;hh.hi[0,0]=second.hi
    return J(value,gg,hh)


def flow_jets(ref,cell,at=None):
    """Value and first two physical-high-rank derivatives of alpha,beta."""
    left,right=cell['left'],cell['right']
    rr=I((right['r']-left['r'])/cell['dz'])
    aa=I((right['a']-left['a'])/cell['dz'])
    if at is None:
        r=I(I(left['r']).lo,I(right['r']).hi)
        a=I(I(left['a']).lo,I(right['a']).hi)
        z=I(I(left['z']).lo,I(right['z']).hi)
        rd,ad=cell['rdata'],cell['adata']
    else:
        rp=left['r']+at*(right['r']-left['r'])
        ap=left['a']+at*(right['a']-left['a'])
        zp=left['z']+at*(right['z']-left['z'])
        r,a,z=I(rp),I(ap),I(zp)
        rd,ad=ref.ranges(rp,rp),ref.ranges(ap,ap)
    RJ=one_jet(rd['F'],rd['phi']*rr,rd['dphi']*rr.square())
    D,N=numerators(I(ref.L),I(F('.135')),cell['branch'],I(ref.S),
                   one_jet(r,rr),one_jet(a,aa),RJ,one_jet(z,1))
    phir=one_jet(rd['phi'],rd['dphi']*rr,rd['ddphi']*rr.square())
    phia=one_jet(ad['phi'],ad['dphi']*aa,ad['ddphi']*aa.square())
    ms=[phia,phia] if cell['branch']=='early' else [phir,phia,phir,phia]
    terms=[]
    for n,m in zip(N,ms):
        nm=n*m
        val=nm.v/D.v
        first=(nm.g.take(0)-val*D.g.take(0))/D.v
        second=(nm.h.take(0,0)-2*first*D.g.take(0)-val*D.h.take(0,0))/D.v
        terms.append((val,first,second))
    if cell['branch']=='early':return terms[0],terms[1]
    return tuple(a+b for a,b in zip(terms[0],terms[1])),tuple(a+b for a,b in zip(terms[2],terms[3]))


def prepare_flow(ref,cells):
    L,S,M0=I(ref.L),I(ref.S),I(F('.135'))
    z0=cells[0]['left']['z'];zend=cells[-1]['right']['z']
    Z=I(F('.135')-(ref.L*z0-z0*z0/2))
    assert Z.lo>0
    alpha_integral=I(0.)
    for cell in cells:
        x,y=cell['left'],cell['right']
        r=I(I(x['r']).lo,I(y['r']).hi);a=I(I(x['a']).lo,I(y['a']).hi);z=I(I(x['z']).lo,I(y['z']).hi)
        D,N=numerators(L,M0,cell['branch'],S,r,a,cell['rdata']['F'],z)
        assert D.lo>0 and all(n.lo>0 for n in N)
        phia,phir=cell['adata']['phi'],cell['rdata']['phi']
        m=[phia,phia] if cell['branch']=='early' else [phir,phia,phir,phia]
        base=[ni*mi/D for ni,mi in zip(N,m)]
        alpha=base[0] if cell['branch']=='early' else base[0]+base[1]
        beta=base[1] if cell['branch']=='early' else base[2]+base[3]
        cell['alpha'],cell['base']=alpha,base
        dz=I(cell['dz']); e=exp_positive(alpha*dz)
        Zcoarse=e*Z+beta/alpha*(e-I(1.))
        # Taylor through order two with a rigorous third-derivative remainder.
        # Each cell lies on one smooth score piece; endpoint derivative
        # enclosures may include both traces without invalidating the bounds.
        aj,bj=flow_jets(ref,cell)
        a0,b0=flow_jets(ref,cell,F(0))
        am,_=flow_jets(ref,cell,F(1,2))
        Za=I(Z.lo,Zcoarse.hi)
        third=(aj[2]+3*aj[0]*aj[1]+aj[0]*aj[0]*aj[0])*Za+(2*aj[1]+aj[0].square())*bj[0]+aj[0]*bj[1]+bj[2]
        first=a0[0]*Z+b0[0]
        second=(a0[1]+a0[0].square())*Z+a0[0]*b0[0]+b0[1]
        Znext=Z+dz*first+dz.square()*second/2+dz.square()*dz*third/6
        assert Znext.lo>=Z.lo
        cell['alpha_mass']=dz*am[0]+dz.square()*dz*aj[2]/24
        assert cell['alpha_mass'].lo>0
        cell['Z']=I(Z.lo,Znext.hi)
        cell['Zleft']=Z
        Z=Znext
        alpha_integral=alpha_integral+cell['alpha_mass']
    Zend=Z
    future=I(0.)
    for cell in reversed(cells):
        # At any point in the cell, future alpha mass is between next-cell
        # mass and that mass plus this cell's entire integral.
        E=exp_positive(I(future.lo,(future+cell['alpha']*I(cell['dz'])).hi))
        ns=[0,1] if cell['branch']=='early' else [0,0,1,1]
        cell['weights']=[E*b*(cell['Z'] if n==0 else I(1.))/Zend for b,n in zip(cell['base'],ns)]
        future=future+cell['alpha_mass']
    return {'z0':str(z0),'zend':str(zend),'Zinitial':float(F('.135')-(ref.L*z0-z0*z0/2)),
            'Zterminal':Zend.bounds(),'alpha_integral':alpha_integral.bounds()}


def tube(ref,tdata,S,reference_lo,reference_hi):
    if reference_hi<=ref.c:
        return np.full(S.lo.shape,float(I(reference_lo).lo)),np.full(S.lo.shape,float(I(reference_hi).hi))
    sig=tdata['F']+(S-I(ref.S))*tdata['u']
    d=I(ref.L)-sig/I(ref.L)
    disc=d.square()-2*S
    floordisc=I(ref.L*ref.L)-2*(sig+S)
    assert np.all(disc.lo>0) and np.all(floordisc.lo>0)
    low=(1-d-disc.sqrt()).lo
    high=(I(ref.L)-floordisc.sqrt()).hi
    return np.maximum(float(I(ref.c).lo),low),np.minimum(float(I(ref.rc).hi),high)


def evaluate_cell(ref,cell,nS,nrank,extra):
    Slo,S_hi=F('.02197280467819'),F('.026650314880436')
    grid=[I(Slo+(S_hi-Slo)*F(i,nS)) for i in range(nS+1)]
    Ss=I(np.array([g.lo for g in grid[:-1]]),np.array([g.hi for g in grid[1:]]))
    left,right=cell['left'],cell['right']
    rl,rh=tube(ref,cell['rdata'],Ss,left['r'],right['r'])
    al,ah=tube(ref,cell['adata'],Ss,left['a'],right['a'])
    # A Taylor remainder needs the entire chord from the reference. The
    # obstacle tube need not be jointly convex in S and rank. Use its global
    # rectangular hull, including the reference ranks, for every S slab.
    rlo=min(float(np.min(rl)),float(I(left['r']).lo))
    rhi=max(float(np.max(rh)),float(I(right['r']).hi))
    alo=min(float(np.min(al)),float(I(left['a']).lo))
    ahi=max(float(np.max(ah)),float(I(right['a']).hi))
    rl=np.full(nS,rlo);rh=np.full(nS,rhi)
    al=np.full(nS,alo);ah=np.full(nS,ahi)
    allS=[];allr=[];alla=[]
    for i in range(nS):
        if rl[i]>rh[i] or al[i]>ah[i]:continue
        rg=np.linspace(rl[i],rh[i],nrank+1);ag=np.linspace(al[i],ah[i],nrank+1)
        for j in range(nrank):
            for k in range(nrank):
                rlo,rhi=rg[j],rg[j+1];alo,ahi=ag[k],ag[k+1]
                if cell['branch']=='early':
                    if rlo>ahi:continue
                    rhi=min(rhi,ahi);alo=max(alo,rlo)
                else:
                    if alo>rhi:continue
                    ahi=min(ahi,rhi);rlo=max(rlo,alo)
                allS.append((Ss.lo[i],Ss.hi[i]));allr.append((rlo,rhi));alla.append((alo,ahi))
    assert allS
    def arr(x):x=np.array(x);return I(x[:,0],x[:,1])
    si,ri,ai=arr(allS),arr(allr),arr(alla)
    S,r,a=J.var(si,0),J.var(ri,1),J.var(ai,2)
    zref=I(I(left['z']).lo,I(right['z']).hi)
    zstart=rational(ref.raw['controls'][0]['z']);zend=rational(ref.raw['controls'][-1]['z'])
    vp=I(-1/(zend-zstart));v=-(zref-I(zstart))/I(zend-zstart)
    z=J(zref)+(S-I(ref.S))*v
    R=J(cell['rdata']['F'])+(S-I(ref.S))*cell['rdata']['u']
    D,N=numerators(I(ref.L),I(F('.135')),cell['branch'],S,r,a,R,z)
    weights=cell['weights'];total=sum(weights,I(0.))
    H=-D.loghess()*total
    for n,w in zip(N,weights):H=H+n.loghess()*w
    factor=1+(si-I(ref.S))*vp
    penalty=total*(vp/factor).square()
    rootdata=[cell['adata'],cell['adata']] if cell['branch']=='early' else [cell['rdata'],cell['adata'],cell['rdata'],cell['adata']]
    for data,w in zip(rootdata,weights):
        m=data['phi']+(si-I(ref.S))*data['du']
        assert np.all(m.lo>0)
        penalty=penalty+w*(data['du']/m).square()
    H.lo[...,0,0]=down(H.lo[...,0,0]-penalty.hi)
    H.hi[...,0,0]=up(H.hi[...,0,0]-penalty.lo)
    aa=H.take(1,1);bb=H.take(1,2);cc=H.take(2,2)
    # Monotonicity of the minimum eigenvalue in diagonal entries and |offdiag|.
    av=I(aa.lo);cv=I(cc.lo);bv=I(np.maximum(abs(bb.lo),abs(bb.hi)))
    mineig=(av+cv-((av-cv).square()+4*bv.square()).sqrt())/2
    mr=up(max(0.,float(-np.min(mineig.lo)))+extra*float(total.hi))
    d1=aa+I(mr);d2=cc+I(mr)-bb.square()/d1
    assert np.all(d1.lo>0) and np.all(d2.lo>0)
    c1,c2=H.take(0,1),H.take(0,2)
    schur=c1.square()/d1+(c2-bb*c1/d1).square()/d2
    ms=float(np.min(down(H.lo[...,0,0]-schur.hi)))
    return {'ms':ms,'mr':float(mr),'boxes':len(allS),'Dmin':float(np.min(D.v.lo)),
            'min_numerator':min(float(np.min(n.v.lo)) for n in N)}


def coverage(ref,cells):
    events={}
    for cell in cells:
        left,right=cell['left'],cell['right'];w=cell['weights']
        branches=[('a',sum(w,I(0.)))] if cell['branch']=='early' else [('r',w[0]+w[2]),('a',w[1]+w[3])]
        for key,weight in branches:
            lo,hi=left[key],right[key]
            slope=I((hi-lo)/cell['dz'])
            assert slope.lo>0
            lower=F(float((weight/(2*slope)).lo))
            events.setdefault(lo,[]).append(lower)
            events.setdefault(hi,[]).append(-lower)
    locations=sorted(set(events)|{ref.c,ref.rc});density=F(0);minimum=None;gaps=[];covered=[]
    for x,y in zip(locations,locations[1:]):
        for event in events.get(x,[]):density+=event
        if y<=ref.c or x>=ref.rc:continue
        if density<=0:gaps.append([str(max(x,ref.c)),str(min(y,ref.rc))])
        else:
            minimum=density if minimum is None else min(minimum,density)
            covered.append([float(max(x,ref.c)),float(min(y,ref.rc))])
    return {'covered_kappa_lower':float(I(minimum).lo),'covered_K_lower':float((I(F(16,9))*I(minimum)).lo),
            'uncovered_rank_intervals':gaps,'covered_range':[covered[0][0],covered[-1][1]]}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--reference',default='research/closure/global/warped_interval_reference.json')
    parser.add_argument('--S-slabs',type=int,default=32)
    parser.add_argument('--rank-slabs',type=int,default=3)
    parser.add_argument('--z-subdivisions',type=int,default=1)
    parser.add_argument('--extra',type=float,default=5.)
    parser.add_argument('--limit',type=int,default=0)
    parser.add_argument('--output',default='research/closure/global/warped_interval_certificate.json')
    args=parser.parse_args();start=time.time()
    ref=Reference(args.reference);gauge_floor=ref.gauge_floor();cells=split_cells(ref,args.z_subdivisions)
    terminal_box=ref.terminal_box()
    flow=prepare_flow(ref,cells);cov=coverage(ref,cells)
    scalar=I(0.);rank=I(0.);rows=[]
    for i,cell in enumerate(cells[:args.limit or None]):
        result=evaluate_cell(ref,cell,args.S_slabs,args.rank_slabs,args.extra)
        dz=I(cell['dz']);scalar=scalar+I(result['ms'])*dz;rank=rank+I(result['mr'])*dz/2
        result.update({'z0':str(cell['left']['z']),'z1':str(cell['right']['z']),'branch':cell['branch']})
        rows.append(result)
        if i%25==0:print(json.dumps({'cell':i,'total':len(cells),'scalar_lower_so_far':float(scalar.lo),'rank_upper_so_far':float(rank.hi),'seconds':time.time()-start}),flush=True)
    ell=I(ref.rc-ref.c);rankloss=4*ell*rank
    answer={'status':'coefficient and reported coverage certificate for the explicit reference; no VI or optimality claimed',
            'arithmetic':'exact rational polynomial ranges; outward nextafter binary64 interval operations; Taylor exponential remainder',
            'reference':args.reference,'settings':vars(args),'flow':flow,'coverage':cov,
            'terminal_box_membership':terminal_box,
            'reference_gauge_derivative_lower':gauge_floor,
            'high_cells_total':len(cells),'high_cells_verified':len(rows),
            'scalar_integral_lower':float(scalar.lo),'rank_integral_upper':float(rank.hi),
            'one_endpoint_rank_loss_upper':float(rankloss.hi),
            'covered_rank_margin_lower':float(down(cov['covered_K_lower']-rankloss.hi)),
            'scalar_margin_if_terminal_curvature_650':float(down(650+scalar.lo)),
            'seconds':time.time()-start,'rows':rows}
    Path(args.output).write_text(json.dumps(answer,indent=2))
    print(json.dumps({k:v for k,v in answer.items() if k!='rows'},indent=2),flush=True)


if __name__=='__main__':main()
