"""Exact endpoint consequences of the ordered-242 calibration budget.
The analytic retained-term inequality is in retained_endpoint_bounds.txt.
"""
from fractions import Fraction as F
import json
from pathlib import Path
class I:
 def __init__(self,a,b=None):
  if isinstance(a,I):self.lo,self.hi=a.lo,a.hi
  else:self.lo,self.hi=F(a),F(a if b is None else b)
 def __add__(self,o):
  o=I(o);return I(self.lo+o.lo,self.hi+o.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,o):return self+-I(o)
 def __rsub__(self,o):return I(o)+-self
 def __mul__(self,o):
  o=I(o);v=[x*y for x in (self.lo,self.hi) for y in (o.lo,o.hi)];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,o):
  o=I(o);assert o.lo>0;return self*I(1/o.hi,1/o.lo)
ref=json.loads(Path('research/closure/root/warped_cubic_ordered_reference_242.json').read_text())
var=json.loads(Path('research/closure/root/transport_cubic_ordered_variation_242.json').read_text())
L=F(str(ref['L']));Ss=F(str(ref['Sstar']));rc=F(str(ref['rc']));q=F(str(ref['terminal_q']))
z0=F(var['flow']['z0']);z1=F(var['flow']['zend'])
budget=F('.000006847496');assert F(str(var['entropy_flux_absorption']['localization_budget_upper']))<budget
Sl,Sh=Ss-F('.000317626822'),Ss+F('.000317626822')
Zlo,Zhi=F(1),F(0)
Q=lambda t:L*t-t*t/2
for i in range(64):
 S=I(Sl+(Sh-Sl)*F(i,64),Sl+(Sh-Sl)*F(i+1,64));z=I(z1)-(S-Ss)
 Bq=L*(Q(I(1-q))-S)/(1-q)
 bar=z*(Q(1-z+q)-S-Bq)/(L-q)
 Zb=I('.135')-S-bar
 Zlo=min(Zlo,Zb.lo);Zhi=max(Zhi,Zb.hi)
Zbar=I(Zlo,Zhi)
assert 0<Zbar.lo and Zbar.hi<F('.025')
flux=F('16.8498');assert -F(str(var['entropy_flux_absorption']['favorable_constant_flux']))>flux
rank=budget/flux
assert rank<F('.0000004064')
remaining=(F('.562330')-rc)*rank+rank*rank/2
assert remaining<F('.0000000870')
# Raw flux + nonincreasing score gives the short lower-cone bound
# without the sharp support bound or a right-endpoint continuity claim.
roughsig=F('.000418')
assert F('.36')+roughsig<F('.38')
assert roughsig*roughsig/2>remaining
# The required local score lower-slope control follows from C>.691.
# If sigma(rc)>=.00024, integrate its Lipschitz lower cone before d=.385.
sig=F('.00024');decay=F('.309')
assert sig/decay<F('.385')-rc
assert sig*sig/(2*decay)>remaining
contact=rc+sig/F('.022');assert contact<F('.36')
# Core alpha floor also follows directly from the global C floor and A ceiling.
Ll,Lh=F('.562325'),F('.562330');Cl=F('.691');amin=F('.2918')
Pmax=Lh*F('.64')-F('.64')**2/2-F('.02271790')
alpha=((2*Cl-1)*Ll+(1-Cl)*amin)/Pmax
assert alpha>F('2.30')
assert Cl+F('2.30')*F('.25')>F('1.26')
# Even the weaker previously certified high-slope excess .08 is enough.
Ehi=F('.025')*budget
separation=F('.08')*(z0-F('.78'))**2/2
assert Ehi<separation
separation782=F('.26')*(z0-F('.782'))**2/2
assert Ehi<separation782
out={'status':'exact rational retained endpoint bounds passed','budget_upper':str(budget),'terminal_Zbar_upper':float(Zbar.hi),'initial_high_deficit_upper':float(Ehi),'high_departure_by_078_deficit_lower':float(separation),'terminal_quantile_displacement_upper':float(rank),'remaining_low_slack_upper':float(remaining),'raw_low_score_slack_upper_on_rc_to_036':'.000418','low_score_slack_upper':'.00024','central_contact_upper':float(contact),'extended_alpha_lower':float(alpha),'extended_high_slope_upper':'-1.26','high_onset_lower_after_bootstrap':'.782','departure_by_0782_deficit_lower':float(separation782)}
Path(__file__).with_name('retained_endpoint_bounds_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
