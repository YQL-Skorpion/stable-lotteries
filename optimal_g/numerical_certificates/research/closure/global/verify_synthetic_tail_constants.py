"""Exact rational C,alpha bounds for transported right-boundary prices."""
from fractions import Fraction as F
from verify_intermediate_low_credit import I
import json
L=I('.562325','.562330');Sl,Sh=F('.02271790'),F('.023354')
Q=lambda x:L*x-x*x/2
stack=[(F('.36'),F('.38'),F('.3058'),F('.36'),Sl,Sh)]
minimumC=minimumA=None;leaves=visited=0
while stack:
 pl,ph,tl,th,sl,sh=stack.pop();visited+=1
 p,tau,S=I(pl,ph),I(tl,th),I(sl,sh)
 R=Q(p)-S;P=Q(1-p)-S
 D=(2*L-tau)*R-(2*p-L)*P
 N=(L-tau)*R+(L-p)*P;J=L*L-tau*p
 cc=F('.81')*D-N;aa=3*D-J
 if D.lo>0 and N.lo>0 and J.lo>0 and cc.lo>0 and aa.lo>0:
  leaves+=1;minimumC=cc.lo if minimumC is None else min(minimumC,cc.lo);minimumA=aa.lo if minimumA is None else min(minimumA,aa.lo);continue
 widths=[ph-pl,th-tl,8*(sh-sl)];j=max(range(3),key=lambda x:widths[x]);a=[pl,ph,tl,th,sl,sh];m=(a[2*j]+a[2*j+1])/2
 assert a[2*j+1]-a[2*j]>F(1,10**10)
 b=a.copy();a[2*j+1]=m;b[2*j]=m;stack.extend([tuple(a),tuple(b)])
join=F('2.8')-F('.81')-3*(F('.38')+F('.14183'))
end=F('6.1')-F('.81')-3*(F('.38')+F('.562330'))
assert join>0 and end>0
out={'status':'exact synthetic right-tail constants passed','p':['.36','.38'],'tau':['.3058','.36'],
 'C_upper':'.81','alpha_upper':'3','visited':visited,'leaves':leaves,
 'C_cleared_margin_lower':float(minimumC),'alpha_cleared_margin_lower':float(minimumA),
 'join_gap_derivative_lower':float(join),'terminal_gap_derivative_lower':float(end)}
print(json.dumps(out,indent=2))
open('research/closure/global/synthetic_tail_constants_certificate.json','w').write(json.dumps(out,indent=2)+'\n')
