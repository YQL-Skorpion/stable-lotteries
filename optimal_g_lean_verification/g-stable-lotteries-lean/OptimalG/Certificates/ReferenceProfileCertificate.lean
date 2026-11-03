import OptimalG.Certificates.ReferenceExactPolynomialBounds

/-! Finite enclosures for the actual cap and polynomial branches of the
reference primitive, score, gauge, and gauge derivative. -/
namespace OptimalG.Certificates
open Set

structure ReferenceProfileBox where
  primitive : IntegerInterval
  score : IntegerInterval
  gauge : IntegerInterval
  gaugeDerivative : IntegerInterval

namespace IntegerInterval

def rationalEndpointsCheck (s : ℕ) (a b : ℚ) (out : IntegerInterval) : Bool :=
  constCheck s a out && constCheck s b out

theorem rationalEndpointsCheck_sound {s : ℕ} {a b : ℚ} {out : IntegerInterval}
    (hc : rationalEndpointsCheck s a b out=true) {x : ℝ}
    (hx : (a:ℝ)≤x ∧ x≤(b:ℝ)) : out.Contains s x := by
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hc
  have ha' := constCheck_sound ha
  have hb' := constCheck_sound hb
  exact ⟨ha'.1.trans (mul_le_mul_of_nonneg_left hx.1 (Nat.cast_nonneg s)),
    (mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg s)).trans hb'.2⟩

end IntegerInterval

namespace ReferenceProfileBox

def capValue (L S r : ℚ) : ℚ := L^2-L/2+L*r/2-L*S/(1-r)
def capScore (L S r : ℚ) : ℚ := L/2-L*S/(1-r)^2

def capCheck (s : ℕ) (L S lo hi : ℚ) (out : ReferenceProfileBox) : Bool :=
  decide (0≤L ∧ 0≤S ∧ lo≤hi ∧ hi<1 ∧ 2*S≤(1-hi)^2) &&
  (IntegerInterval.rationalEndpointsCheck s (capValue L S lo) (capValue L S hi) out.primitive &&
   IntegerInterval.rationalEndpointsCheck s (capScore L S hi) (capScore L S lo) out.score &&
   IntegerInterval.rationalEndpointsCheck s (-L/(1-hi)) (-L/(1-lo)) out.gauge &&
   IntegerInterval.rationalEndpointsCheck s (-L/(1-hi)^2) (-L/(1-lo)^2) out.gaugeDerivative)

theorem capCheck_sound {s : ℕ} (L S lo hi : ℚ) (out : ReferenceProfileBox)
    (hc : out.capCheck s L S lo hi=true) {r : ℝ} (hr : r∈Icc (lo:ℝ) hi) :
    out.primitive.Contains s (cap L S r) ∧
    out.score.Contains s (capSlope L S r) ∧
    out.gauge.Contains s (-(L:ℝ)/(1-r)) ∧
    out.gaugeDerivative.Contains s (-(L:ℝ)/(1-r)^2) := by
  obtain ⟨hgeom,hnum⟩ := Bool.and_eq_true_iff.mp hc
  have hq : 0≤L ∧ 0≤S ∧ lo≤hi ∧ hi<1 ∧ 2*S≤(1-hi)^2 := of_decide_eq_true hgeom
  have hL : (0:ℝ)≤L := by exact_mod_cast hq.1
  have hS : (0:ℝ)≤S := by exact_mod_cast hq.2.1
  have hhi : (hi:ℝ)<1 := by exact_mod_cast hq.2.2.2.1
  have hsafe : (2:ℝ)*S≤(1-(hi:ℝ))^2 := by exact_mod_cast hq.2.2.2.2
  have hlo : (lo:ℝ)≤hi := hr.1.trans hr.2
  have hhiMem : (hi:ℝ) ∈ Iic (hi:ℝ) := by
    change (hi:ℝ) ≤ hi
    exact le_rfl
  have hm := cap_monotone_prefix hL hS hhi hsafe
  have hp := capSlope_antitone_prefix hL hS hhi
  have hg := capGauge_antitone_prefix hL hhi
  have hd := capGaugeDerivative_antitone_prefix hL hhi
  have hcap : cap L S lo≤cap L S r ∧ cap L S r≤cap L S hi :=
    ⟨hm hlo hr.2 hr.1,hm hr.2 hhiMem hr.2⟩
  have hscore : capSlope L S hi≤capSlope L S r ∧ capSlope L S r≤capSlope L S lo :=
    ⟨hp hr.2 hhiMem hr.2,hp hlo hr.2 hr.1⟩
  have hgauge : -(L:ℝ)/(1-hi)≤-(L:ℝ)/(1-r) ∧ -(L:ℝ)/(1-r)≤-(L:ℝ)/(1-lo) :=
    ⟨hg hr.2 hhiMem hr.2,hg hlo hr.2 hr.1⟩
  have hderiv : -(L:ℝ)/(1-hi)^2≤-(L:ℝ)/(1-r)^2 ∧ -(L:ℝ)/(1-r)^2≤-(L:ℝ)/(1-lo)^2 :=
    ⟨hd hr.2 hhiMem hr.2,hd hlo hr.2 hr.1⟩
  rcases Bool.and_eq_true_iff.mp hnum with ⟨hab,hdu⟩
  rcases Bool.and_eq_true_iff.mp hab with ⟨hps,hu⟩
  rcases Bool.and_eq_true_iff.mp hps with ⟨hF,hphi⟩
  refine ⟨IntegerInterval.rationalEndpointsCheck_sound hF ?_,
    IntegerInterval.rationalEndpointsCheck_sound hphi ?_,
    IntegerInterval.rationalEndpointsCheck_sound hu ?_,
    IntegerInterval.rationalEndpointsCheck_sound hdu ?_⟩
  · simpa [capValue,cap] using hcap
  · simpa [capScore,capSlope] using hscore
  · simpa using hgauge
  · simpa using hderiv

def primitivePolynomial (p : CubicPiece) : RationalPolynomial :=
  [p.f0,p.a0,p.a1/2,p.a2/3,p.a3/4]
def scorePolynomial (p : CubicPiece) : RationalPolynomial := [p.a0,p.a1,p.a2,p.a3]

theorem primitivePolynomial_eval (p : CubicPiece) (x : ℝ) :
    (primitivePolynomial p).eval x=p.primitive x := by
  simp [primitivePolynomial,RationalPolynomial.eval,CubicPiece.primitive]
  ring

theorem scorePolynomial_eval (p : CubicPiece) (x : ℝ) :
    (scorePolynomial p).eval x=p.score x := by
  simp [scorePolynomial,RationalPolynomial.eval,CubicPiece.score]
  ring

def centralCheck (s k : ℕ) (p : CubicPiece) (g dg : RationalPolynomial)
    (c d lo hi : ℚ) (out : ReferenceProfileBox) : Bool :=
  decide (c<d ∧ lo<hi) &&
  (profilePolynomialCheck s k (primitivePolynomial p) (lo-p.lo) (hi-p.lo) out.primitive &&
   profilePolynomialCheck s k (scorePolynomial p) (lo-p.lo) (hi-p.lo) out.score &&
   profilePolynomialCheck s k g ((lo-c)/(d-c)) ((hi-c)/(d-c)) out.gauge &&
   profilePolynomialCheck s k dg ((lo-c)/(d-c)) ((hi-c)/(d-c)) out.gaugeDerivative)

theorem centralCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (p : CubicPiece) (g dg : RationalPolynomial) (c d lo hi : ℚ)
    (out : ReferenceProfileBox) (hc : out.centralCheck s k p g dg c d lo hi=true)
    {r : ℝ} (hr : r∈Icc (lo:ℝ) hi) :
    out.primitive.Contains s (p.primitive (r-p.lo)) ∧
    out.score.Contains s (p.score (r-p.lo)) ∧
    out.gauge.Contains s (g.eval ((r-c)/((d:ℝ)-c))) ∧
    out.gaugeDerivative.Contains s (dg.eval ((r-c)/((d:ℝ)-c))) := by
  obtain ⟨hgeom,hnum⟩ := Bool.and_eq_true_iff.mp hc
  have hq : c<d ∧ lo<hi := of_decide_eq_true hgeom
  have hcd : (0:ℝ)<(d:ℝ)-c := by exact_mod_cast sub_pos.mpr hq.1
  have hp : lo-p.lo<hi-p.lo := sub_lt_sub_right hq.2 _
  have hp' : r-(p.lo:ℝ)∈Icc ((lo-p.lo:ℚ):ℝ) ((hi-p.lo:ℚ):ℝ) := by
    simpa only [mem_Icc,Rat.cast_sub] using
      And.intro (sub_le_sub_right hr.1 (p.lo:ℝ)) (sub_le_sub_right hr.2 (p.lo:ℝ))
  have hg : (lo-c)/(d-c)<(hi-c)/(d-c) :=
    (div_lt_div_iff_of_pos_right (sub_pos.mpr hq.1)).mpr (sub_lt_sub_right hq.2 c)
  have hg' : (r-c)/((d:ℝ)-c)∈Icc (((lo-c)/(d-c):ℚ):ℝ) (((hi-c)/(d-c):ℚ):ℝ) := by
    simp only [mem_Icc,Rat.cast_div,Rat.cast_sub]
    exact ⟨div_le_div_of_nonneg_right (sub_le_sub_right hr.1 (c:ℝ)) hcd.le,
      div_le_div_of_nonneg_right (sub_le_sub_right hr.2 (c:ℝ)) hcd.le⟩
  rcases Bool.and_eq_true_iff.mp hnum with ⟨hab,hdu⟩
  rcases Bool.and_eq_true_iff.mp hab with ⟨hps,hu⟩
  rcases Bool.and_eq_true_iff.mp hps with ⟨hF,hphi⟩
  refine ⟨?_,?_,profilePolynomialCheck_sound hs hk g _ _ _ hu hg hg',
    profilePolynomialCheck_sound hs hk dg _ _ _ hdu hg hg'⟩
  · simpa only [primitivePolynomial_eval] using
      profilePolynomialCheck_sound hs hk (primitivePolynomial p) _ _ _ hF hp hp'
  · simpa only [scorePolynomial_eval] using
      profilePolynomialCheck_sound hs hk (scorePolynomial p) _ _ _ hphi hp hp'

end ReferenceProfileBox
end OptimalG.Certificates
