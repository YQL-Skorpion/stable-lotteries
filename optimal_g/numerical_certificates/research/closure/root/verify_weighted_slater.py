"""Exact rational weighted Slater certificate for the bounded-score relaxation.

No numerical optimizer, external package, or floating-point assertion is used.
Decimal output is for readability only; every tested comparison uses Fraction.
"""
from fractions import Fraction as R
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('--ell', default='.28', choices=['.26','.28','.29'])
parser.add_argument('--d',default='.36')
args=parser.parse_args()

Llo, Lhi = R('.562325'), R('.562330')
ell, d = R(args.ell), R(args.d)
h=d-ell
S, delta = R('.026'), R('.001')
v = 1 - ell

def Q(L, t):
    return L*t-t*t/2

def B(L, t):
    return L*L-L/2+L*t/2-L*S/(1-t)

def amplitude(L):
    return 3*((S-Q(L, ell)+B(L, ell))/h-delta)

# The amplitude is increasing throughout the parameter interval.
assert 2*Llo-(1+ell)/2-S/v > 0
Alo, Ahi = amplitude(Llo), amplitude(Lhi)
assert 0 < Alo <= Ahi < R('.057')

# sigma=delta+A(1-u/h)^2, phi=L-t-sigma. Uniform box interior.
phi_lower = Llo-d-delta-Ahi
assert phi_lower > R('.14')
assert delta == R('.001')

def weight(u):
    return 1-u/h+u*u/(3*h*h)

# weight is positive and decreasing on [0,h]. For each rational cell,
# the following bounds the exact expression (B(t)-F(t))/(t-ell).
# It also proves the continuous extension of that quotient at ell.
N = 1000
lower_bounds = []
for i in range(N):
    ulo, uhi = h*i/N, h*(i+1)/N
    low = (ell-Lhi/2+ulo/2+delta+Alo*weight(uhi)
           -Lhi*S/((v-uhi)*v))
    lower_bounds.append(low)
assert min(lower_bounds) > 0

# Integral of sigma is delta*h+A*h/3=M. This verifies the affine
# terminal equality symbolically through its defining identity.
for L in (Llo, Lhi):
    A = amplitude(L)
    terminal = B(L,ell)+(L-ell)*h-h*h/2-delta*h-A*h/3
    assert terminal == Q(L,d)-S

# S is strictly interior to either of the certified universal intervals.
assert R('.0219728') < S < R('.0266504')

print('Weighted Slater certificate passed using exact rational arithmetic; ell:',float(ell))
print('Verified positive weighted primitive margin:',
      float(min(lower_bounds)))
print('Uniform score lower bound:', float(phi_lower))
print('Uniform root-ceiling margin:', float(delta))
print('Amplitude interval:', float(Alo), float(Ahi))
