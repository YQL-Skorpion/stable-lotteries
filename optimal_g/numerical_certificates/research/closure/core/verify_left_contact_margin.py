"""Exact arithmetic for the left-contact exclusion.

This checks the numerical implications of the separately proved transport
localizer and mixed KKT hypotheses. It does not assert those hypotheses.
"""
from fractions import Fraction as F

Lmin, Lmax = F('.562325'), F('.562330')
Smax = F('.023354')
cref = F('.2950935005377889')
Cmin = F('.116')
Jmax = F('.000007149525')

# On [c,cref], with c>=.285, the magnitude of the rational-cap curvature
# increases with rank, L and S.
cap_curvature_max = 2*Lmax*Smax/(1-cref)**3
assert cap_curvature_max < F('.074987345523')
curvature_gap = Cmin-cap_curvature_max
assert curvature_gap > 0

# The initial first-hit atom is no larger than the total BV energy J.
# Integrating the root ceiling to that first hit bounds the primitive gap.
primitive_gap_max = (Lmax-cref)*Jmax
excluded_contact = F('.2854')
forced_gap = curvature_gap*(cref-excluded_contact)**2/2
assert forced_gap > primitive_gap_max

# Transfer from L to L+delta, with S_new=S+.20delta and low primitive
# F_new=F+.18delta, increases the cap gap at cref. Both coefficients in
# the exact quadratic difference are positive on the parameter box.
linear_transfer_min = 2*Lmin-F('.68')+cref/2-(Smax+F('.2')*Lmin)/(1-cref)
quadratic_transfer = 1-F('.2')/(1-cref)
assert linear_transfer_min > F('.399')
assert quadratic_transfer > 0

print('Conditional exact left-contact exclusion verified: c > 0.2854.')
for name in ['cap_curvature_max', 'primitive_gap_max', 'forced_gap',
             'linear_transfer_min', 'quadratic_transfer']:
    print(name, float(globals()[name]))
print('strict gap margin', float(forced_gap-primitive_gap_max))

# Optional sharpening: if the BV entropy proof retains its exact singular
# recession coefficient W0=3 (rather than reducing it to 8W0/9), then the
# same certificate gives c>.2867. The basic result above does not need it.
budget = F('.000006847495738')
positional_loss = F('1.708911325')
singular_mass_max = budget/(3-positional_loss)
sharp_gap_max = (Lmax-cref)*singular_mass_max
sharp_forced_gap = curvature_gap*(cref-F('.2867'))**2/2
assert sharp_forced_gap > sharp_gap_max
print('Optional exact-recession sharpening: c > 0.2867.')
print('singular_mass_max', float(singular_mass_max))
