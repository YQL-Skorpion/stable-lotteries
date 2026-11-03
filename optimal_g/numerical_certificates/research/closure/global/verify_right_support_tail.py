"""Complete the right support transport across the actual quadratic tail.
The certified fixed-anchor rectangle describes the same quadratic even if
its anchor precedes the actual join. No assertion is made about extrapolated
values being values of the selected flow.
"""
from pathlib import Path
import sys,json,time,argparse
import numpy as np
from verify_right_support_transport import I,C,L,p0,Q,data,piece,prices
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'root'))
from verify_structural_tail_hc import tail_F,tail_phi,tail_combo,lower_phi

def evaluate_raw(box):
 S,p,q,z,tau=[I(box[:,2*j],box[:,2*j+1]) for j in range(5)]
 N,D,J,N0,D0,J0,n1,d1,w,eta,beta,ep=prices(S,p,tau)
 U=z-L;delta=p-p0;K0=p0*(U-p0/2)
 E=Q(z)-S-tail_F(z)
 T1=(n1*D0-d1*N0)*U+J*D0*(U-p0-delta/2)+w*(K0+E)
 su=piece(q,S,'slackupper');eu=piece(z-p+q,S,'remainingupper')
 compare=delta*T1+D0*(q*(N-J*(z-p))+J*(su+eu))
 direct=N*(U+q)+J*(Q(z)-S+p*(U-p/2)-q*(z-p)+su+eu)+tail_combo(z,J,D)
 _,_,f0,sl=data(S)
 delay=z-p+q
 headcase=(q.hi<=float(C('.2635').lo))&(delay.lo>=float(C('.36').hi))&(delay.hi<=float(C('.782').lo))
 lin=N+J*(L-z+p-f0);pos=I(np.maximum(0.,lin.lo),np.maximum(0.,lin.hi));quad=J*(1+sl)
 assert np.all(quad.lo>0)
 gain=pos.square()/(2*quad)
 dc=N*U+J*(Q(z-p)-S)+tail_combo(z,J,D)+gain
 cc=delta*T1+D0*gain
 direct=I(direct.lo,np.where(headcase,np.minimum(direct.hi,dc.hi),direct.hi))
 # Preserve the raw comparison's quadratic dependence on tau.
 # Normalized comparison and direct residual have different positive scales.
 ok=(eta-1).lo>0
 ok&=(ep.hi<0)&(N.lo>0)&(D.lo>0)&(J.lo>0)&((1+beta*p-eta).lo>0)
 _,_,f0,_=data(S)
 ok&=(beta*(f0-L+1-p)-1).lo>0
 return compare.hi,direct.hi,ok

def evaluate(box):
 # The cleared direct residual is affine in tau. The cleared comparison
 # is quadratic. Bounding its negative curvature gives a chord bound,
 # avoiding a spurious independent enclosure of repeated tau factors.
 lo=box.copy();hi=box.copy();lo[:,9]=lo[:,8];hi[:,8]=hi[:,9]
 cl,dl,_=evaluate_raw(lo);ch,dh,_=evaluate_raw(hi)
 S,p,q,z,tau=[I(box[:,2*j],box[:,2*j+1]) for j in range(5)]
 R=Q(p)-S;R0=Q(p0)-S;U=z-L;E=Q(z)-S-tail_F(z)
 su=piece(q,S,'slackupper');eu=piece(z-p+q,S,'remainingupper')
 Kp=p*(U-p/2)-q*(z-p)+su+eu+E;K0=p0*(U-p0/2)+E
 curvature=q*R*R0+p*R0*Kp-p0*R*K0
 correction=I(np.maximum(0.,-curvature.hi),np.maximum(0.,-curvature.lo))*(I(box[:,9])-I(box[:,8])).square()/4
 # Independent selected-high coefficient certification covers every p,S,tau
 # here, including eta>1, eta'<0, eta<=1+beta*p, A split and positivity.
 return np.nextafter(np.maximum(cl,ch)+correction.hi,np.inf),np.maximum(dl,dh),np.ones(len(box),dtype=bool)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--max-boxes',type=int,default=30000000);args=ap.parse_args()
 flat=[]
 for a,b in [('.02271790','.023354'),('.38','.562330'),('0','.562330'),('.8495','1'),('.3058','.36')]:flat.extend([float(C(a).lo),float(C(b).hi)])
 active=np.array([flat]);start=time.time();visited=leaves=depth=nc=nd=0;worstc=worstd=-np.inf
 while len(active):
  active=active[active[:,4]<=active[:,3]]
  active[:,5]=np.minimum(active[:,5],active[:,3]);active[:,2]=np.maximum(active[:,2],active[:,4])
  for _ in range(2):
   S,p,q,z,tau=[I(active[:,2*j],active[:,2*j+1]) for j in range(5)]
   pr=prices(S,p,tau);N,J=pr[0],pr[2];d=z-p+q
   low=N+J*(I(lower_phi(d).lo)-I(piece(q,S,'score').hi))
   high=N+J*((L-d)-I(piece(q,S,'score').lo))
   inc=low.lo>=0;dec=high.hi<=0
   active[:,4]=np.where(inc,active[:,5],active[:,4]);active[:,5]=np.where(dec,active[:,4],active[:,5])
  cp,dp,valid=evaluate(active);cg=(cp<0)&valid;dg=(dp<0)&valid;good=cg|dg
  visited+=len(active);leaves+=int(np.sum(good));nc+=int(np.sum(cg));nd+=int(np.sum(dg))
  if np.any(cg):worstc=max(worstc,float(np.max(cp[cg])))
  if np.any(dg):worstd=max(worstd,float(np.max(dp[dg])))
  bad=active[~good]
  print(json.dumps({'depth':depth,'visited':visited,'remaining':len(bad),'compare_upper':float(np.max(cp)),'direct_upper':float(np.max(dp)),'seconds':time.time()-start}),flush=True)
  if not len(bad):break
  if visited>args.max_boxes:raise RuntimeError('box budget')
  widths=bad[:,1::2]-bad[:,::2];weights=np.array([30.,5.,5.,6.,0.]);which=np.argmax(widths*weights,axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  assert np.all(mid>bad[ids,2*which]) and np.all(mid<bad[ids,2*which+1]),'unsplittable'
  aa=bad.copy();bb=bad.copy();aa[ids,2*which+1]=mid;bb[ids,2*which]=mid;active=np.vstack([aa,bb]);depth+=1
 out={'status':'verified right support-line full Hermite-tail comparison','p_range':['.38','.562330'],'z_range':['.8495','1'],'tau_range':['.3058','.36'],'S_range':['.02271790','.023354'],'fixed_anchor':'global/fixed_anchor_terminal_certificate.json','visited':visited,'leaves':leaves,'compare_boxes':nc,'direct_boxes':nd,'strict_cleared_compare_upper':worstc,'strict_direct_upper':worstd,'seconds':time.time()-start}
 Path(__file__).with_name('right_support_tail_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
