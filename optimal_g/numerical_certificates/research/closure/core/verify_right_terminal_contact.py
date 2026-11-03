"""Exact exclusion of binary contact at the selected right boundary .875."""
from verify_binary_high import I,J,certify,BOX,vals,records
from fractions import Fraction as F
from pathlib import Path
import json
records.clear()
p=I('.875');hh=I('.125')
def N(L,S,q):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 return (2*(L-q)*(L-q-ph(q))-2*(S-Q(q)+B(q))-hh*hh)/2
certify('q endpoint .2761 positive',lambda L,S:N(L,S,I('.2761')),BOX)
certify('q endpoint .2764 negative',lambda L,S:-N(L,S,I('.2764')),BOX)
def data(L,S,q):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S);si=L-q-ph(q)
 Y=p*(hh-si);H=1-2*p-si+p*hh/(L-q)
 return Y,H
D=BOX+[I('.2761','.2764')]
certify('terminal Y above .0829',lambda L,S,q:data(L,S,q)[0]-I('.0829'),D)
certify('terminal Y below .0840',lambda L,S,q:I('.0840')-data(L,S,q)[0],D)
certify('terminal barrier slope below -.396',lambda L,S,q:-I('.396')-data(L,S,q)[1],D)
# Root of B'(t)=L-t and slope location of its rational side.
certify('synthetic contact above .30782',lambda L,S:L-I('.30782')-vals(L,S)[3](I('.30782')),BOX)
certify('synthetic contact below .30865',lambda L,S:vals(L,S)[3](I('.30865'))-L+I('.30865'),BOX)
certify('synthetic rational slope magnitude below .1',lambda L,S:I('.1')-2*L*S/(1-I('.30865'))**3,BOX)

def coefficients(L,S,r,c):
 Q=lambda t:L*t-t*t/2
 b=I(max(r.lo,c.lo),max(r.hi,c.hi));A=L-c;B=L-b
 R=Q(r)-S;P=Q(1-r)-S;h=2*L-c;k=r+b-L;D=h*R-k*P
 C=(A*R+B*P)/D;al=(k*A+h*B)/D
 K=Q(p-r)-S-I('.0829')
 H=-C*(p-L)-al*K
 return D,C,al,K,H

def certify4(name,fn,target='0'):
 domain=BOX+[I('.25','.36'),I('.30782','.30865')];stack=[(domain,0)];floor=None;n=0
 while stack:
  box,depth=stack.pop()
  try:out=fn(*box);ok=out.lo>F(target)
  except (AssertionError,ZeroDivisionError):ok=False;out=I(-100,100)
  if ok:floor=out.lo if floor is None else min(floor,out.lo);n+=1;continue
  assert depth<45,(name,[(float(x.lo),float(x.hi)) for x in box],float(out.lo),float(out.hi))
  j=max(range(4),key=lambda j:(box[j].hi-box[j].lo)*[5,5,1,1][j]);mid=(box[j].lo+box[j].hi)/2
  for lo,hi in [(box[j].lo,mid),(mid,box[j].hi)]:
   child=box.copy();child[j]=I(lo,hi);stack.append((child,depth+1))
 records[name]={'leaves':n,'strict_lower':str(floor),'decimal_lower':float(floor)};print(name,n,float(floor),flush=True)
certify4('corner determinant positive',lambda L,S,r,c:coefficients(L,S,r,c)[0]-I('.05'))
certify4('corner support slope above .1',lambda L,S,r,c:coefficients(L,S,r,c)[1]-I('.1'))
certify4('corner support slope below 1',lambda L,S,r,c:1-coefficients(L,S,r,c)[1])
certify4('corner alpha positive',lambda L,S,r,c:coefficients(L,S,r,c)[2])
certify4('central increment K positive',lambda L,S,r,c:coefficients(L,S,r,c)[3])
certify4('all synthetic cap slopes above -.388',lambda L,S,r,c:coefficients(L,S,r,c)[4]+I('.388'))
# All-root coefficient signs for replacing scores and primitive. The root
# rank ranges are broad; these do not require the corner reduction.
L=BOX[0];S=BOX[1];r=I('.25','.36');a=I('.285','.38');b=I('.285','.38')
R=L*r-r*r/2-S;P=L*(1-r)-(1-r)**2/2-S;h=2*L-a;k=r+b-L
K=L*(p-r)-(p-r)**2/2-S-I('.0829');U=p-L
# kA+hB remains positive for all positive synthetic scores in [.18,.27].
Jmin=(I('.25')+I('.285')-BOX[0])*I('.28')+(2*BOX[0]-I('.38'))*I('.18')
assert Jmin.lo>0
# k may be negative only by .02733; other terms positive.
cA=U*I('.085')-I('.02733')*I('.06')
assert cA.lo>0
records['score_primitive_monotonicity']={'J_lower':str(Jmin.lo),'cA_lower':str(cA.lo),'conditions':'R>=.085, K<=.06, Bsynthetic>=.18, Asynthetic<=.28; checked below'}
# Establish the coarse bounds used above directly on actual domains by
# simple endpoint estimates, rather than trusting independent wide I ranges.
Rmin=F('.562325')*F('.25')-F('.25')**2/2-F('.023354')
assert Rmin>F('.085')
Kmax=F('.562330')**2/2-F('.02271790')-F('.0829')
assert Kmax<F('.06')
assert F('.562325')-F('.38')>F('.18')
assert F('.562330')/2-F('.562325')*F('.02271790')/(1-F('.285'))**2<F('.28')
out=Path(__file__).with_name('right_terminal_contact_certificate.json');out.write_text(json.dumps(records,indent=2)+'\n')
print('Right terminal boundary contact excluded, slope gap > .008:',out)
