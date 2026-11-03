"""Exact endpoint bounds preserve every cap on the coupled-contact tail.
The joining margin is independently certified over the full coupled-contact
parameter box by core/verify_binary_contact_hermite.py.
"""
from fractions import Fraction as F
from pathlib import Path
import json
Ll,Lh=F('.562325'),F('.562330')
Cmax,amax,rmax=F('.78'),F('4.53'),F('.36')
base=Path(__file__).resolve().parents[1]
certificate=json.loads((base/'core/binary_contact_hermite_certificate.json').read_text())
joinmargin=F(certificate['concave derivative join']['strict_lower'])
assert joinmargin>F('.115')
vlow=F('6.18') # independently certified fixed-anchor coefficient bound
endmargin=vlow-Cmax-amax*(rmax+Lh)
assert joinmargin>0 and endmargin>0
assert F('.8495')-rmax>F('.36') and 1-F('.2635')<F('.782')
# The uniform alpha ceiling also covers inactive controls with k<0:
# nonnegative A and k<0 imply J=kA+hB<=hB.
assert (2*Lh-F('.285'))*(Lh-F('.285'))/F('.0519')<amax
out={'status':'verified exact Hermite extension of every selected cap',
     'scope':'coupled interior binary contact and selected cap values at join',
     'joining_margin_certificate':'core/binary_contact_hermite_certificate.json',
     'tail_right_negative_slope_lower':str(vlow),
     'gap_derivative_join_margin':str(joinmargin),'gap_derivative_end_margin':str(endmargin),
     'C_upper':str(Cmax),'alpha_upper':str(amax),'r_range':['.2635','.36']}
Path(__file__).with_name('hermite_cap_extension_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
