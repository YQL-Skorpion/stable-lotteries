"""Exact constants for layers [.25,.36], independent roots [.285,.38].
This certifies a necessary-family normal form, not a matching full upper.
"""
from fractions import Fraction as F
from math import comb, factorial
import json
from pathlib import Path
Llo,Lhi=F('.562325'),F('.562330')
rlo,rhi=F('.25'),F('.36'); amin,amax=F('.285'),F('.38')
Smax,Smin=F('.0267'),F('.02197280467819')
# Before plateau formation only the original LP lower bound is available.
Soriginal_min=F('.02196')
mu=F('.00025509854'); rho=F('2.98')
Ulo,Uhi=F('.775')-Lhi,F('.313')
Rlo,Kmax,Dlo=F('.0826'),F('.159'),F('.0519')
kmax=F('.178'); Pmax=F('.135'); Q=lambda L,t:L*t-t*t/2
B=lambda L,S,t:L*(Q(L,1-t)-S)/(1-t)
def bern(p,s,w):
 n=len(p)-1
 u=[sum((p[i]*comb(i,j)*s**(i-j)*w**j for i in range(j,n+1)),F(0)) for j in range(n+1)]
 return [sum((u[j]*F(comb(k,j),comb(n,j)) for j in range(k+1)),F(0)) for k in range(n+1)]
def exp_upper(x):
 return sum((x**n/F(factorial(n)) for n in range(11)),F(0))+(x**11/F(factorial(11)))/(1-x/12)
assert Q(Llo,rlo)-Smax>Rlo
assert Q(Lhi,1-rhi)-Soriginal_min+(1+rho)*mu<Pmax
assert rhi/(Llo-rhi)<rho<Llo/(1-rlo-Llo)
assert rho*mu<F('.0149752779577') # inherited available slack below .245
hmin=2*Llo-amax;k0=amax-Llo
p=[-hmin*Smax-k0*(Lhi-F('.5')),hmin*Llo-(Lhi-F('.5'))-k0*(1-Lhi),-hmin/2-(1-Lhi)+k0/2,F(1,2)]
db=bern(p,rlo,rhi-rlo)
assert min(db)-kmax*mu>Dlo
assert (3*Llo-rhi-2*amax)*rho-kmax>0
# Coupled-r opposite binary polynomial; never mix R(rlo) with P(rhi).
op=bern([-Llo*Smax,Llo**2-Lhi+F('.5')+Soriginal_min-mu,-Llo/2+Lhi-1,F('.5')],rlo,rhi-rlo)
assert min(op)>F('.0143')
Jmax=Lhi**2-amin**2
assert Jmax/Dlo<F('4.53')
HP=Jmax*(Uhi*F('.136')+kmax*Kmax)/Dlo**2
assert HP<F('6.19')
rn=Lhi-amin;kn=Lhi-rlo-amin
assert Rlo-kn*Kmax/Ulo>0
assert rn/(Rlo-kn*Kmax/Ulo)<F('4.47')<F('4.53')
assert Uhi*rn/Dlo<F('1.68')<F('6.19')
assert min(r*(Ulo-r/2) for r in [rlo,rhi])-mu>0
loss=F('6.19')/F('4.53')*(exp_upper(F('.453'))-1)
assert loss<F('.784')
assert F('.875')/(Llo-F('.28'))<F('3.100')
assert rho+1-F('.784')-F('3.100')==F('.096')
assert 1-F('.784')==F('.216')
# Active/nearactive third score, valid before nonnegative normalization.
Amax=Lhi-amin;hmax=2*Lhi-amin;E=Lhi-F('.5')
coefU=lambda r:Llo*(Q(Llo,r)-Smax)-(r+k0)*(Pmax+Amax*r)
assert min(coefU(rlo),coefU(rhi))>0
p=[Ulo*(-Llo*Smax-k0*Pmax)-k0*Amax*E,Ulo*(Llo*Llo-Pmax-k0*Amax)-Amax*E,Ulo*(-Llo/2-Amax)+k0*Amax/2,Amax/2]
tb=bern(p,rlo,rhi-rlo)
Kbudget=F('.111315');assert Uhi**2/2+E<Kbudget
den=Uhi*Pmax+hmax*Kbudget
assert min(tb)/den>F('.0332')
# D<.116 by k>=0 or r<rn respectively.
assert hmax*F('.136')<F('.116')
assert Q(Lhi,rn)<F('.118') and hmax*F('.118')+kn*Pmax<F('.116')
assert (min(tb)-F('.005')*F('.116'))/den>F('.0289')
cAlo=Ulo*Rlo-kn*Kbudget
assert cAlo>F('.0145')
# Root-max and running-maximum reattachment estimates are unchanged.
assert Q(Lhi,F('.385'))-Smax-B(Lhi,Smax,F('.345'))>F('.0065')
assert Q(Llo,F('.385'))-Q(Llo,amax)-mu>F('.000644')
recordgap=Q(Llo,amax)-Q(Llo,F('.37'))-mu
assert recordgap/F('.01')-F('.005')>F('.1568')
# Exact auxiliary margins in the consolidated normal-form proof.
Sprecise=F('.0266503148804352')
# Central values are below the binary cap throughout [.38,.385].
assert B(Llo,Smin,amax)-Q(Llo,amax)+Smin>F('.002449158')
assert Q(Lhi,F('.37'))-Smax-B(Lhi,Smax,F('.345'))>F('.0037')
# Positivity of the support coefficient C for active first-root minimizers.
B0=Lhi-amin;E0=Lhi-F('.5')-Smin
ur_floor=Ulo*(Q(Llo,rlo)-Smax-B0*rlo)-B0*(E0-rlo*rlo/2)
assert ur_floor>F('.00030254668')
assert B0>Ulo and Llo>B0 # derivative on [rlo,amin] is positive
for rr in [amin,rhi]:
 assert Ulo*(Llo-Lhi+rr)+E0+Lhi*rr-F(3,2)*rr*rr>0
# The last derivative is concave, so endpoint positivity covers [amin,rhi].
# Compact class uses weaker ordinary average, not retained-slack constraint.
af=(Q(Lhi,F('.35'))-Smax-B(Lhi,Smax,F('.34')))/F('.01')-F('.035')
assert af>F('.0618')
assert af-F('.005')*F('.116')/cAlo>F('.0218')
# Universal C<=1 used in exposure. N-D <= -LR+rP follows box ceilings.
assert min(op)>0
# The binary-dependent D bound is sharper after plateau formation.
Dcompact=hmax*Lhi*Pmax/(1-rhi)+kn*Pmax
assert Dcompact<F('.104')
aflocal=(Q(Lhi,F('.35'))-F('.0234')-B(Lhi,F('.0234'),F('.34')))/F('.01')-F('.035')
Plocal=Q(Llo,1-rlo)-Smax
assert (aflocal*Rlo+F('.0332')*Plocal)/Dcompact>F('.116')
# cA/cB<.74 under binaries and postplateau root budget.
rm=F(10)
for i in range(64):
 x=rlo+(rhi-rlo)*F(i,64);y=rlo+(rhi-rlo)*F(i+1,64)
 Pu=Q(Lhi,1-y)-Smin
 assert F('.74')*(1-x)-Llo<0
 for j in range(64):
  u=Ulo+(Uhi-Ulo)*F(j,64);v=Ulo+(Uhi-Ulo)*F(j+1,64)
  Kf=min(x*(u-x/2),y*(u-y/2));Kc=F('.74')*(2*Llo-amax)-(y+amax-Llo)
  assert Kc>0
  m=v*Pu*(F('.74')*(1-y)-Lhi)+Kf*(1-y)*Kc
  assert m>0;rm=min(rm,m)
assert F('.74')<Llo/(1-rlo)
# Monotone L comparison on nonnegative low class.
Pmin=Q(Llo,1-rlo)-Smax
EL=-2*Ulo*Rlo-Ulo*Pmin+(2*Kmax-Pmin)*Amax
assert EL<F('-.0027')
out={'status':'verified exact rational necessary-family constants','layers':['.25','.36'],'independent_roots':['.285','.38'],'rho':str(rho),'D_lower':str(Dlo),'D_Bernstein':[str(x) for x in db],'alpha_upper':'4.53','HP_upper':'6.19','integrated_P_loss_upper':str(loss),'phase1_terminal_gain':'.096','phase2_terminal_gain':'.216','opposite_binary_margin_lower':str(min(op)),'active_B_lower':'.0332','nearactive_B_lower':'.0289','nearactive_A_lower':'.0218','common_KKT_score_floor':'.02','cA_lower':str(cAlo),'original_scalar_lower':str(Soriginal_min),'active_C_numerator_lower':str(ur_floor),'cleared_ratio_margin_lower':str(rm),'EL_upper':str(EL)}
Path(__file__).with_name('layer_extension_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
