"""Small exact constants used in both post-contact binary ranges."""
from verify_binary_high import I,J,certify,BOX,vals,records
import json
from pathlib import Path
records.clear()
def pa(L,S):
 a=I('.2918');b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 return 1-(2*(L-a)*(L-a-ph(a))-2*(S-Q(a)+B(a))).sqrt()
certify('rational terminal h above .085',lambda L,S:1-pa(L,S)-I('.085'),BOX)
certify('rational terminal p above .9125',lambda L,S:pa(L,S)-I('.9125'),BOX)
certify('rational terminal p below .915',lambda L,S:I('.915')-pa(L,S),BOX)
def headN(L,S,h):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S)
 nc=(2*(L-b)*(L-b-ph(b))-2*(S-Q(b)+B(b))-h*h)/2
 return nc-(L-b)*I('.00026')
certify('head N positive .085 to .10',headN,BOX+[I('.085','.10')])
assert (I('.00024')+I('.309')*(I('.348541')-I('.2635')-I('.085'))).hi<I('.00026').lo

def Na(L,S,h):
 b,Q,B,ph,A,be,fh,sg,H2=vals(L,S);a=I('.2918')
 sig=L-a-ph(a);nc=(2*(L-a)*sig-2*(S-Q(a)+B(a))-h*h)/2
 sigend=I('.00024')+I('.309')*(I('.348541')-a-h).pos()
 return nc-(L-a)*sigend
certify('prefix endpoint N positive .02 to .06765',Na,BOX+[I('.02','.06765')])
certify('automatic ranks q>=.337',lambda L,S:I('.5')-(I('2.122')+140*(S-I('.02271790')))*(L-I('.337')),BOX)
out=Path(__file__).with_name('binary_tail_constants_certificate.json');out.write_text(json.dumps(records,indent=2)+'\n');print(out)
