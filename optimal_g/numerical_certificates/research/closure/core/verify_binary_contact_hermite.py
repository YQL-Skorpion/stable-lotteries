"""Exact coupled terminal shape, conditional on interior rational binary contact."""
from verify_binary_high import I,J,certify,BOX,vals,records
import json
from pathlib import Path
records.clear()
def contact(L,S,q):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 sigma=L-q-ph(q)
 h=(2*(L-q)*sigma-2*(S-Q(q)+B(q))).sqrt()
 z=1-h;Y=z*(h-sigma);H=1-2*z-sigma+z*h/(L-q)
 c1=-6*Y/h-4*H+2;c2=3*H-3+6*Y/h
 return z,Y,H,c1/h,(c1+2*c2)/h,c2
D=BOX+[I('.2635','.28')]
for j,(name,lo,hi) in enumerate([('z','.8495','.8836'),('Y','.0798','.0926'),('H','-.429','-.313'),('initial slope','-3.6','-2.8'),('terminal slope','-6.5','-6.1'),('quadratic coefficient','-.27','-.15')]):
 certify(name+' lower',lambda L,S,q,j=j,lo=lo:contact(L,S,q)[j]-I(lo),D)
 certify(name+' upper',lambda L,S,q,j=j,hi=hi:I(hi)-contact(L,S,q)[j],D)
def join(L,S,q):
 z,Y,H,initial,terminal,c2=contact(L,S,q)
 return -I('.78')+I('4.53')*(H-(L-z+I('.36')))-initial
certify('concave derivative join',join,D)
# Initial score remains strictly below root ceiling; then the slope <-2.8
# keeps the whole Hermite tail below it, positive primitive follows from
# negativity of the score together with endpoint primitive zero.
certify('initial root ceiling gap',lambda L,S,q:L-contact(L,S,q)[0]-contact(L,S,q)[2],D)
out=Path(__file__).with_name('binary_contact_hermite_certificate.json');out.write_text(json.dumps(records,indent=2)+'\n')
print('All exact coupled Hermite bounds passed:',out)
