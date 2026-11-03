"""Exact cap-contact upper bound from the remaining slack area."""
from fractions import Fraction as F
import json
from verify_intermediate_low_credit import I
Ll,Lh=F('.562325'),F('.562330');Sl,Sh=F('.02271790'),F('.023354')
c=F('.305');rc=F('.348541');Eend=F('.000000087')
# Ecap - sigma_cap*(rc-c) - Eend is affine and increasing in S.
# Its L-dependence is checked on a rational interval.
L=I(Ll,Lh);S=I(Sl)
Q=L*c-c*c/2
B=L*L-L/2+L*c/2-L*S/(1-c)
sigma=L-c-(L/2-L*S/(1-c)**2)
res=S-Q+B-sigma*(rc-c)-Eend
Sder=1-L/(1-c)-L*(rc-c)/(1-c)**2
assert res.lo>F('.00002') and Sder.lo>0
# On [.305,rc], sigma_cap'<0. Its zero occurs before .313.
assert 1-2*Lh*Sh/(1-rc)**3>0
assert F('.313')-Lh/2-Lh*Sh/(1-F('.313'))**2>0
print(json.dumps({'status':'exact last cap c<.305 certificate passed',
 'area_gap_at_0305_lower':float(res.lo),'S_derivative_lower':float(Sder.lo),
 'argument':'gap derivative in c is -sigma_cap_prime*(rc-c)>0; cap contact cannot occur after sigma_cap turns negative'},indent=2))
# Every primitive up to .53 is below B: the retained cap supplies the low
# part, and the central/high root ceiling supplies the part above .36.
S=I(Sl,Sh);q=F('.18');b=F('.2635')
phi0=2*L*(L-F('.5'))/b+L/2-L*S*(2/(b*(1-b))-1/(1-b)**2)
phib=L/2-L*S/(1-b)**2;head_slope=(phib-phi0)/b
remaining=max((p*(2*L-1-q-phi0-head_slope*q)+p*p/2-S).hi for p in [F('.65'),F('.775')])
assert remaining<F('-.006')
assert 1-2*Lh*Sh/(1-F('.53'))**3>0
assert F('.36')-Lh/2-Lh*Sh/(1-F('.36'))**2>0
t=F('.36')
Efloor=L*L-L/2-L*t/2+t*t/2+I(Sl)*(1-L/(1-t))
assert Efloor.lo>0
assert 2*Lh*Sh/(1-b)**3 < F('.1')
assert head_slope.hi < -F('.6')
print(json.dumps({'status':'binary remaining-rank constants passed',
 'derivative_at_q_018_upper':float(remaining),'central_B_cap_margin_lower':float(Efloor.lo)},indent=2))
assert 2*Lh*Sh/(1-F('.305'))**3<F('.1')
