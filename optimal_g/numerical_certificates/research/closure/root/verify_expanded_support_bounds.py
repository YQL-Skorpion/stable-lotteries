"""Exact rational support/contact bounds for expanded layers [.25,.36].

Hypotheses are the continuous last cap contact c>.2854, invariant slack
band .022, S<=.023354, root budget and opposite binary bound. The C upper
bound uses only root ceilings and the cumulative root budget.
"""
from fractions import Fraction as F
import json
from pathlib import Path

Ll,Lh=F('.562325'),F('.562330')
Sl,Sh=F('.02271790'),F('.023354')
rl,rh=F('.25'),F('.36')
Q=lambda L,t:L*t-t*t/2

def certify_C(t0,threshold):
    fmin=Ll/2-Lh*Sh/(1-t0)**2
    hmax=2*Lh-t0
    bounds=[]
    for left,right,phase in [(rl,t0,0),(t0,rh,1)]:
        for i in range(4096):
            lo=left+(right-left)*i/4096
            hi=left+(right-left)*(i+1)/4096
            xl,xh=Ll/(1-lo),Lh/(1-hi)
            if phase==0:
                num=fmin*(xl+1)
                den=hmax*xh+Lh-lo-t0
            else:
                num=fmin*xl+Ll-hi-F('.022')
                den=hmax*xh+Lh-2*lo
            assert den>0
            bounds.append(num/den)
    assert min(bounds)>threshold,(float(min(bounds)),float(threshold))
    return min(bounds)

def certify_contact(old,new,C):
    k=1-C
    sig=lambda L,S,c:L/2-c+L*S/(1-c)**2
    area=lambda L,S,c:S-L*c+c*c/2+L*L-L/2+L*c/2-L*S/(1-c)
    smax=sig(Lh,Sh,old)
    assert sig(Ll,Sl,new)>0
    assert -1+2*Lh*Sh/(1-new)**3+k<0
    assert smax*Lh/(k*(1-new)**2)-(1-Lh/(1-new))<0
    assert smax/k*(F(1,2)+Sh/(1-new)**2)-(2*Ll-(1+new)/2-Sh/(1-new))<0
    margin=sig(Lh,Sh,new)**2/(2*k)-area(Lh,Sh,new)
    assert margin>0,float(margin)
    return margin

def certify_upper():
    # C_R=-P J/D^2<0 on active caps, so use R=Q(r)-S.
    # At the two ceiling scores, N-D=-L R+r P<0. Consequently
    # the ceiling-score bound decreases in both a and b. Its maximum
    # has a=.285, b=max(.285,r). Certify .78D-N>0 directly.
    margins=[]
    opposites=[]
    for left,right in [(rl,F('.285')),(F('.285'),rh)]:
        for i in range(1024):
            r0=left+(right-left)*i/1024
            r1=left+(right-left)*(i+1)/1024
            b0=max(F('.285'),r0);b1=max(F('.285'),r1)
            for j in range(128):
                s0=Sl+(Sh-Sl)*j/128;s1=Sl+(Sh-Sl)*(j+1)/128
                R0=Q(Ll,r0)-s1;R1=Q(Lh,r1)-s0
                P0=Q(Ll,1-r0)-s1;P1=Q(Lh,1-r1)-s0
                opposites.append(Ll*R0-r1*P1)
                x0=(2*F('.78')-1)*Ll+(1-F('.78'))*F('.285')
                # .78D-N=x R+[(1-.78)b-.78r-(1-.78)L]P.
                y0=(1-F('.78'))*b0-F('.78')*r1-(1-F('.78'))*Lh
                assert y0<0
                margins.append(x0*R0+y0*P1)
    assert min(opposites)>0
    assert min(margins)>0,float(min(margins))
    return min(margins),min(opposites)

steps=[]
c=F('.2854')
for C,new in [(F('.6809'),F('.2913')),(F('.6907'),F('.2918'))]:
    lower=certify_C(c,C)
    margin=certify_contact(c,new,C)
    steps.append({'c_old':str(c),'C':str(C),'C_exact_lower':str(lower),'c_new':str(new),'contact_margin':str(margin)})
    c=new
last=certify_C(c,F('.691'))
upper,opp=certify_upper()
out={'status':'verified exact expanded support bounds','layer_interval':['.25','.36'],'root_interval':['.285','.38'],'S_interval':[str(Sl),str(Sh)],'bootstrap':steps,'C_lower':'.691','C_exact_lower':str(last),'c_lower':'.2918','C_upper':'.78','upper_margin':str(upper),'opposite_margin':str(opp)}
Path(__file__).with_name('expanded_support_bounds_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
