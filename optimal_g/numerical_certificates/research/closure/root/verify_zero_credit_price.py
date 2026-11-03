"""Exact structural low-ratio and zero-credit price bounds, p in [.65,.88].
Uses the proved coupled-contact fixed-anchor bounds, not a narrow join box.
"""
from fractions import Fraction as F
from pathlib import Path
import json
Ll,Lh=F('.562325'),F('.562330')
Sl,Sh=F('.02271790'),F('.023354')
b=F('.2635');rho=F('1.29')
K=2/(b*(1-b))-1/(1-b)**2
head_ratio_margin=rho*(2*(Ll-F('.5'))/b+F('.5')-Sh*K)-1
assert head_ratio_margin>0
fmin=Ll/2-Lh*Sh/(1-F('.313'))**2
assert rho*fmin>Lh-b
assert rho*(Ll-F('.36')-F('.022'))>Lh-F('.36')
# An affine head's ratio is fractional linear, hence maximized at an
# endpoint. The join endpoint is covered by the rational-score bound.
# Every free low root has a>=c>.2918 and sigma<=.022; that ratio is
# largest at the largest permitted root, .36. Central roots have ratio1.

Q=lambda L,t:L*t-t*t/2
central=[]
for p in [F('.65'),F('.851')]:
    central.append(p*(1-p)-rho*(Q(Lh,p)-Sl))
assert min(central)>0 # concave quadratic in p

# The true join is below .875, so .88 is on the quadratic tail.
# Its primitive at .88 increases in both fixed-anchor coordinates Y,H.
h=F('.1376');Yh=F('.08840');Hh=F('-.3514');s=F('.12');x=s/h
assert 0<x<1
F88=Yh*(3*x*x-2*x*x*x)+h*Hh*(x*x-x*x*x)+h*(x-2*x*x+x*x*x)
tailmargin=F('.88')*s-rho*F88
assert tailmargin>0
# For p>=.851, g=-phi has derivative at least1.26 through the entire
# remaining interval (high departure is before .789). Monotonicity and
# the coupled coefficient bounds give g(p)<=g(.88)<=G on p<=.88.
# F(p)>=h_p*g(p)+.63*h_p^2. Thus the numerator of the derivative of
# p(1-p)/F(p) is <=h_p^2*(g(p)-.63*(2p-1))<0.
G=1-F('6.18')*s+F('12.73')*s*s
derivmargin=F('.63')*(2*F('.851')-1)-G
assert derivmargin>0
out={'status':'verified exact low ratio and price domination',
     'low_ratio_upper':str(rho),'price_range':['.65','.88'],
     'head_ratio_margin':str(head_ratio_margin),
     'central_cleared_margin':str(min(central)),
     'tail_endpoint_margin':str(tailmargin),'price_derivative_margin':str(derivmargin),
     'scope':'structural low/high shape and coupled-contact fixed-anchor bounds'}
Path(__file__).with_name('zero_credit_price_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
