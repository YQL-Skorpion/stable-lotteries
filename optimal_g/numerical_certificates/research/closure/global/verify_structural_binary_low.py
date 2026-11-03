"""Exact constants proving every binary inequality for p<=.65."""
from fractions import Fraction as F
import json
from verify_intermediate_low_credit import I
Ll,Lh=F('.562325'),F('.562330');Sl,Sh=F('.02271790'),F('.023354')
L=I(Ll,Lh);S=I(Sl,Sh);b=F('.2635')
Q=lambda t:L*t-t*t/2
phi0=2*L*(L-F('.5'))/b+L/2-L*S*(2/(b*(1-b))-1/(1-b)**2)
phib=L/2-L*S/(1-b)**2
slope=(phib-phi0)/b
headmin=F(1);midmin=F(1)
for i in range(1024):
 p=I(b*i/1024,b*(i+1)/1024)
 # Divide the q=0 binary slack by p before treating p=0.
 gap=L*(phi0+slope*p/2)-(Q(1-p)-S)
 headmin=min(headmin,gap.lo)
 p=I(b+(F('.64')-b)*i/1024,b+(F('.64')-b)*(i+1)/1024)
 gap=p*(L*L-L+F('.5'))+p*p*(L/2-1)+p*p*p/2+S*(p-L)
 midmin=min(midmin,gap.lo)
assert headmin>0 and midmin>0
# p in [.64,.65] follows exactly from F(1-p)<=B_S(1-p).
# This cap is retained on ranks [.35,.36].
margin=min(p*(1+F('.436')-2*Lh)-p*p/2+Sl for p in [1-Lh,F('.65')])
assert margin>F('.0138')
# The derivative in q>=L is at most F(p)-p(1-p).
# This convex quadratic has its maximum at an endpoint.
high=max(Lh*p-p*p/2-Sl-p*(1-p) for p in [Ll,F('.65')])
assert high<0
print(json.dumps({'status':'every binary constraint p<=.65 proved structurally',
 'head_q0_slack_divided_by_p_lower':float(headmin),'middle_q0_slack_lower':float(midmin),
 'q0_last_piece':'retained cap on [ .35,.36 ]', 'low_q_derivative_numerator_margin':float(margin),
 'high_q_derivative_upper':float(high)},indent=2))
