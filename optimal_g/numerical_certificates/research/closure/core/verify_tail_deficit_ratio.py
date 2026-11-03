"""Exact coupled affine bound on the normalized Hermite terminal deficit."""
from verify_binary_high import I,J,certify,BOX,records
from verify_binary_contact_hermite import contact
import json
from pathlib import Path
records.clear()
D=BOX+[I('.2635','.2764')]
def uppergap(L,S,q):
 z,Y,H,sp0,sp1,c2=contact(L,S,q);k0=-1-sp1/2
 return I('2.122')+140*(S-I('.02271790'))-k0
certify('affine S upper normalized deficit',uppergap,D)
def hmono(L,S,q):
 z,Y,H,sp0,sp1,c2=contact(L,S,q)
 return 1+sp1/2-c2/(3*(1-z)**2)
certify('normalized deficit decreases in h',hmono,D)

def refined(L,S,q,h):
 z,Y,H,sp0,sp1,c2=contact(L,S,q);k0=-1-sp1/2;n=c2/(3*(1-z)**2)
 ss=S-I('.02271790');A=I('2.122')+140*ss;B=-I('3.774')-700*ss
 return A+B*h-k0-n*h
certify('mid tail numerator at h .02',lambda L,S,q:refined(L,S,q,I('.02')),D)
certify('mid tail numerator at h .09',lambda L,S,q:refined(L,S,q,I('.09')),D)
out=Path(__file__).with_name('tail_deficit_ratio_certificate.json');out.write_text(json.dumps(records,indent=2)+'\n');print(out)
