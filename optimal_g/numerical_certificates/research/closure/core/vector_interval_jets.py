"""First-order interval jets using the project's outward-rounded arithmetic."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'global'))
from interval_warped_hessian import I
class J:
 n=5
 def __init__(self,v,g=None):self.v=I(v);self.g=[I(0)]*self.n if g is None else g
 @classmethod
 def var(cls,v,j):
  a=cls(v);a.g=a.g.copy();a.g[j]=I(1);return a
 def __add__(self,y):
  y=y if isinstance(y,J) else J(y);return J(self.v+y.v,[a+b for a,b in zip(self.g,y.g)])
 __radd__=__add__
 def __neg__(self):return J(-self.v,[-a for a in self.g])
 def __sub__(self,y):return self+-y if isinstance(y,J) else self+-I(y)
 def __rsub__(self,y):return -self+y
 def __mul__(self,y):
  y=y if isinstance(y,J) else J(y);return J(self.v*y.v,[a*y.v+self.v*b for a,b in zip(self.g,y.g)])
 __rmul__=__mul__
 def reciprocal(self):return J(1/self.v,[-a/self.v.square() for a in self.g])
 def __truediv__(self,y):return self*(y if isinstance(y,J) else J(y)).reciprocal()
 def __rtruediv__(self,y):return self.reciprocal()*y
 def square(self):return J(self.v.square(),[2*self.v*a for a in self.g])
 def sqrt(self):
  v=self.v.sqrt();return J(v,[a/(2*v) for a in self.g])

def mx(x,y):
 if not isinstance(x,J) and not isinstance(y,J):
  x=I(x);y=I(y);return I(np.maximum(x.lo,y.lo),np.maximum(x.hi,y.hi))
 x=x if isinstance(x,J) else J(x);y=y if isinstance(y,J) else J(y)
 first=x.v.lo>=y.v.hi;second=y.v.lo>=x.v.hi
 g=[I(np.where(first,a.lo,np.where(second,b.lo,np.minimum(a.lo,b.lo))),np.where(first,a.hi,np.where(second,b.hi,np.maximum(a.hi,b.hi)))) for a,b in zip(x.g,y.g)]
 return J(mx(x.v,y.v),g)
def mn(x,y):return -mx(-x,-y)
