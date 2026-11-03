"""Exact split-q derivative margin with the original .2635 affine head.

Use the layer-dependent lower price, rather than taking its separate
minimum. Conditional on the support bounds in verify_critical_dual_price.py
and central high onset beyond .782. No sampled inequality is used.
"""
from fractions import Fraction as F
from pathlib import Path
import json

class I:
    def __init__(self,a,b=None):
        if isinstance(a,I):self.lo,self.hi=a.lo,a.hi
        else:self.lo,self.hi=F(a),F(a if b is None else b)
    def __add__(self,b):
        b=I(b);return I(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-I(b)
    def __rsub__(self,b):return I(b)+-self
    def __mul__(self,b):
        b=I(b);v=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b);assert b.lo>0;return self*I(1/b.hi,1/b.lo)

Ll,Lh=F('.562325'),F('.562330')
Sl,Sh=F('.02271790'),F('.023354')
rl,rh=F('.25'),F('.36')
c=F('.2918');head=F('.2635');onset=F('.782')
Q=lambda L,t:L*t-t*t/2

def residual(L,S,r,early):
    M=L/2-L*S/F('.72')**2
    R=Q(L,r)-S;P=Q(L,1-r)-S
    N=M*R+(L-r)*P
    D=(L+M)*R-(2*r-L)*P
    b=I(c) if early else r
    score=L/2-L*S/(1-c)**2 if early else L-r-F('.022')
    price_num=((b+r-L)*N+score*D)*(1-r)
    price_den=L*P*N
    phi0=2*L*(L-F('.5'))/head+L/2-L*S*(2/(head*(1-head))-1/(1-head)**2)
    gap=phi0-L+onset-r
    return price_num*gap-price_den,N,D,price_num,price_den,gap

stack=[(Ll,Lh,Sl,Sh,rl,c,True),(Ll,Lh,Sl,Sh,c,rh,False)]
visited=leaves=0;minimum=None;relative=None
while stack:
    ll,lh,sl,sh,xl,xh,early=stack.pop();visited+=1
    v,N,D,num,den,gap=residual(I(ll,lh),I(sl,sh),I(xl,xh),early)
    if v.lo>0 and min(N.lo,D.lo,num.lo,den.lo,gap.lo)>0:
        leaves+=1
        minimum=v.lo if minimum is None else min(minimum,v.lo)
        relative=v.lo/den.hi if relative is None else min(relative,v.lo/den.hi)
        continue
    widths=[(lh-ll)*20,(sh-sl)*5,xh-xl]
    j=max(range(3),key=lambda j:widths[j])
    vals=[ll,lh,sl,sh,xl,xh];a,b=vals[2*j:2*j+2];m=(a+b)/2
    assert b-a>F(1,10**12),(vals,early,float(v.lo))
    left=vals[:];right=vals[:];left[2*j+1]=m;right[2*j]=m
    stack.append((*right,early));stack.append((*left,early))

out={'status':'verified exact coupled split-q margin',
     'head_join':str(head),'central_high_until':str(onset),
     'L_interval':[str(Ll),str(Lh)],'S_interval':[str(Sl),str(Sh)],
     'layer_interval':[str(rl),str(rh)],'rational_prefix_through':str(c),
     'leaves':leaves,'visited':visited,
     'cleared_margin_lower':str(minimum),'relative_margin_lower':str(relative)}
Path(__file__).with_name('critical_split_coupled_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
