"""Coupled rational-contact Hermite bounds at fixed anchor .8624.
The actual contact is constrained by z*<=.875. The anchor may precede it;
its polynomial data are extrapolated, not actual selected-flow samples.
"""
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from interval_warped_hessian import I
C=lambda x:I(F(x))
class V:
 def __init__(self,v,g=None):
  self.v=I(v);self.g=I(np.zeros(self.v.lo.shape+(3,))) if g is None else g
 @staticmethod
 def var(v,j):
  ans=V(v);ans.g.lo[...,j]=1;ans.g.hi[...,j]=1;return ans
 def __add__(self,o):
  o=o if isinstance(o,V) else V(o);return V(self.v+o.v,self.g+o.g)
 __radd__=__add__
 def __neg__(self):return V(-self.v,-self.g)
 def __sub__(self,o):return self+(-o if isinstance(o,V) else -I(o))
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,V) else V(o);return V(self.v*o.v,self.g*o.v.axis()+self.v.axis()*o.g)
 __rmul__=__mul__
 def reciprocal(self):return V(1/self.v,-self.g/self.v.square().axis())
 def __truediv__(self,o):return self*(o if isinstance(o,V) else V(o)).reciprocal()
 def __rtruediv__(self,o):return self.reciprocal()*o
 def square(self):return V(self.v.square(),2*self.v.axis()*self.g)
 def sqrt(self):
  w=self.v.sqrt();return V(w,self.g/(2*w.axis()))
def quantities(L,S,q):
 QQ=lambda t:L*t-t.square()/2
 B=L*L-L/2+L*q/2-L*S/(1-q)
 ph=L/2-L*S/(1-q).square();sg=L-q-ph
 h=(2*(L-q)*sg-2*(S-QQ(q)+B)).sqrt();z=1-h
 Y=z*(h-sg);H=1-2*z-sg+z*h/(L-q)
 # Collected forms reduce removable cancellation in v and g.
 v=2+(6-4*h)*sg/h.square()-2*(1-h)/(L-q)
 g=3*(2-h)*sg/(h.square()*h)-3*(1-h)/((L-q)*h)
 s=F('.1376')
 Ya=s-v*(s*s/2)+g*(s*s*s/3)
 Ha=-1+v*s-g*(s*s)
 E=QQ(z)-S-Y
 return z,Ya,Ha,E,v,g

def evaluate(box):
 vals=[I(box[:,2*j],box[:,2*j+1]) for j in range(3)]
 jets=quantities(*[V.var(x,j) for j,x in enumerate(vals)])
 centers=[I((x.lo+x.hi)/2) for x in vals];cv=quantities(*centers)
 outs=[]
 for j,jet in enumerate(jets):
  mean=cv[j]
  for k in range(3):mean=mean+jet.g.take(k)*(vals[k]-centers[k])
  outs.append(I(np.maximum(jet.v.lo,mean.lo),np.minimum(jet.v.hi,mean.hi)))
 return outs

def main():
 dom=[('.562325','.562330'),('.02271790','.023354'),('.2635','.28')];flat=[]
 for a,b in dom:flat.extend([float(C(a).lo),float(C(b).hi)])
 seed=[]
 for i in range(16):
  for j in range(4):
   row=flat.copy();row[4]=flat[4]+(flat[5]-flat[4])*i/16;row[5]=flat[4]+(flat[5]-flat[4])*(i+1)/16;row[2]=flat[2]+(flat[3]-flat[2])*j/4;row[3]=flat[2]+(flat[3]-flat[2])*(j+1)/4
   if i==15:row[5]=flat[5]
   if j==3:row[3]=flat[3]
   seed.append(row)
 active=np.array(seed);width0=np.array(flat[1::2])-np.array(flat[::2])
 limits=[('.08793','.08840'),('-.3589','-.3514'),('0','.00290'),('6.18','6.42'),('10.77','12.73')]
 count=leaves=excluded=depth=0;boundslo=np.full(5,np.inf);boundshi=np.full(5,-np.inf)
 while len(active):
  out=evaluate(active);count+=len(active)
  outside=out[0].lo>float(C('.875').hi);excluded+=int(np.sum(outside))
  good=~outside
  for j,(a,b) in enumerate(limits):good&=(out[j+1].lo>float(C(a).hi))&(out[j+1].hi<float(C(b).lo))
  leaves+=int(np.sum(good))
  for j in range(5):
   if np.any(good):boundslo[j]=min(boundslo[j],float(np.min(out[j+1].lo[good])));boundshi[j]=max(boundshi[j],float(np.max(out[j+1].hi[good])))
  bad=active[~(good|outside)]
  print(json.dumps({'depth':depth,'visited':count,'remaining':len(bad),'leaves':leaves,'excluded':excluded}),flush=True)
  if not len(bad):break
  if count>4000000:raise RuntimeError('box budget')
  widths=(bad[:,1::2]-bad[:,::2])/width0;widths[:,0]*=.03;which=np.argmax(widths,axis=1);ids=np.arange(len(bad));mid=(bad[ids,2*which]+bad[ids,2*which+1])/2
  a=bad.copy();b=bad.copy();a[ids,2*which+1]=mid;b[ids,2*which]=mid;active=np.vstack([a,b]);depth+=1
 result={'status':'verified fixed-anchor bounds for coupled rational terminal contact','anchor':'.8624','domain':dom,'additional_constraint':'zstar<=.875','visited':count,'leaves':leaves,'excluded_boxes':excluded,'certified_targets':dict(zip(['Y_anchor','H_anchor','E_join','v','g'],limits)),'actual_enclosure':dict(zip(['Y_anchor','H_anchor','E_join','v','g'],[[float(a),float(b)] for a,b in zip(boundslo,boundshi)])),'scope':'anchor values may be polynomial extrapolations before the actual join'}
 Path(__file__).with_name('fixed_anchor_terminal_certificate.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
