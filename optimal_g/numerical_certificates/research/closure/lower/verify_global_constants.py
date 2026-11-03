"""Independent rational replay of the constants used in slack relocation.

No optimizer is used by verification. The optional --pack action snapshots
the initial rank-constraint labels, whose exact formulas are in exact_dual.
"""
import argparse,json
from fractions import Fraction as F
from types import SimpleNamespace
from collections import defaultdict
from exact_dual import ExactVerifier

ap=argparse.ArgumentParser();ap.add_argument('--pack',action='store_true');args=ap.parse_args()
base='research/closure/lower/'
loc=json.load(open(base+'localization200.json'))
if args.pack:
 from adaptive_moving import FineRelaxation
 lp=FineRelaxation(loc['N'],loc['L'])
 json.dump({'N':lp.N,'L':str(lp.L),'labels':lp.labels},open(base+'certified_base_labels.json','w'))
initial=json.load(open(base+'certified_base_labels.json'))
lp=SimpleNamespace(N=initial['N'],L=initial['L'],labels=initial['labels'])
ver=ExactVerifier(lp);N=lp.N;off=N+1;L=F(lp.L)

def evaluate(c,proof):
 residual=defaultdict(F,c);constant=F(0)
 for i,num,den in proof['multipliers']:
  pi=F(num,den)
  assert pi<=0 and i<len(lp.labels)
  row,rhs=ver.row(i);constant+=pi*rhs
  for j,v in row.items():residual[j]-=pi*v
 penalty=sum((v*(ver.caps[j]if v<0 else ver.floors[j])for j,v in residual.items()),F(0))
 assert constant==F(*proof['constant']) and penalty==F(*proof['penalty'])
 return constant+penalty

for rec in loc['proofs']:
 tag=rec['tag'];_,pi,i,j,k,l,z0,z1,x,y=tag;ri=N-pi
 r=F(ri,N);a=F(i+j,2*N);b=F(k+l,2*N);z=F(z0+z1,2*N)
 assert 0<r<1-L and 0<=i<j<=pi and ri<=k<l<=N and a<L and b<L
 assert z-L>=r/2 and F(str(x))>=0 and F(str(y))>=0
 kap=r+b-L
 if kap<0:
  assert F('.26')<=r<=F('.36') and L<=F('.57') and z-L+4*kap>0
 cx={pi:F(1),ri:-F(str(x))}
 cy={off+z1:F(-N),off+z0:F(N),off+z1-ri:F(N),off+z0-ri:F(-N),ri:-F(str(y))}
 assert evaluate(cx,rec['xproof'])>=0
 assert evaluate(cy,rec['yproof'])>=0
 lp.labels.append(tag)

central=json.load(open(base+'full_central_certificate.json'))
i,j=map(lambda t:round(t*N),central['interval'])
lower=evaluate({j:F(1),i:F(-1)},central['proof'])
Q=lambda t:L*t-t*t/2
mu=Q(F(j,N))-Q(F(i,N))-lower
assert mu==F(*central['rational'])
envelopes=json.load(open(base+'uniform_envelope_certificates.json'))
for rec in envelopes['bounds']:
 i=round(rec['rank']*N);sgn=rec['sign']
 assert evaluate({i:F(sgn)},rec['proof'])==F(*rec['bound'])
R=F(*envelopes['bounds'][0]['bound'])+Q(F(26,100))-Q(F(35,100))
P=-F(*envelopes['bounds'][1]['bound'])
S=Q(F(1,2))-F(*envelopes['bounds'][4]['bound'])
margin=F('0.562325')*R-F('.35')*(P+mu)
assert mu<F('.0002551') and S<F('.0267') and margin>F('.001828')
print('All sequential ratio certificates and final envelopes verified with rational arithmetic.')
print('Central slack upper:',float(mu))
print('Uniform R lower:',float(R),'uniform P upper:',float(P))
print('S(.5) upper:',float(S),'post-removal opposite-q0 margin:',float(margin))
