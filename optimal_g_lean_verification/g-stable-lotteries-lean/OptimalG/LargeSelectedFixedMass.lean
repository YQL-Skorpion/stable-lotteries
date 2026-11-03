import OptimalG.LargeSelectedRankReduction
import OptimalG.LargeSelectedEnvelopeBounds

namespace OptimalG
open Set Variational Certificates.LargeSelectedExpressions

/-- Six scalar inequalities cover all low split ranks at mass .65. -/
structure LargeSelectedRankSigns (lam S z : ℝ) : Prop where
  headHead : 0≤headHeadDerivative lam S z
  headFlat : 0≤headFlatDerivative lam S z
  cap : capMaximum lam S z≤0
  left : atMass lam S z (1459/5000) (capDeficit lam S (1459/5000))≤0
  right : atMass lam S z lam 0≤0
  kink : atMass lam S z (Certificates.LargeSelectedExpressions.kink lam S) 0≤0

theorem largeSelected_fixedMass_nonpos {lam S z q : ℝ}
    (hz : z∈Icc (391/500:ℝ) (7/8)) (hq : q∈Icc (0:ℝ) lam)
    (hs : 0≤1+Certificates.SmallMassExpressions.slope lam S)
    (hprod : lam*S≤3/200) (hE : 0≤capDeficit lam S (1459/5000))
    (hslack : 0<capSlack lam S (1459/5000))
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hn : LargeSelectedRankSigns lam S z) :
    largeSelectedNumerator lam S z q (cubic lam S z)
      (largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S)) (13/20)≤0 := by
  have hcap (r : ℝ) (hr : r∈Icc (527/2000:ℝ) (1459/5000)) :
      atMass lam S z r (capDeficit lam S r)≤0 := by
    apply flatNumerator_cap_nonpos (by norm_num : (0:ℝ)<13/20) hprod hr
    convert! hn.cap using 1 <;> dsimp [capMaximum,atMass,headFlatDerivative] <;> ring
  by_cases hqh : q≤527/2000
  · rw [largeRemainingLower,if_pos hqh]
    change largeSelectedNumerator lam S z q (cubic lam S z) (largeHeadRemaining lam S q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S)) (13/20)≤0
    have hm := largeSelected_head_monotone (e:=cubic lam S z) hz hs hcapOrder hn.headHead hn.headFlat
      ⟨hq.1,hqh⟩ (show (527/2000:ℝ)∈Icc 0 (527/2000) by constructor <;> norm_num) hqh
    apply hm.trans
    have hflat : 313/1000≤z-13/20+527/2000 := by linarith only [hz.1]
    have hj := headPrimitive_at_join (527/2000) (cap lam S (527/2000))
      (capScore lam S (527/2000)) (by norm_num)
    change Certificates.SmallMassExpressions.primitive lam S (527/2000)=cap lam S (527/2000) at hj
    have he : largeHeadRemaining lam S (527/2000)=capDeficit lam S (527/2000) := by
      rw [largeHeadRemaining,hj]
      unfold capDeficit
      ring
    simpa only [largeSelectedNumerator,largeRemainingUpper_eq_flat hflat,he,atMass,
      flatNumerator,areaSlope,flat,primitiveCap] using hcap (527/2000) ⟨le_rfl,by norm_num⟩
  · have hflat : 313/1000≤z-13/20+q := by linarith only [hz.1,lt_of_not_ge hqh]
    rw [largeSelectedNumerator,largeRemainingUpper_eq_flat hflat,largeRemainingLower,if_neg hqh]
    by_cases hqw : q≤1459/5000
    · rw [if_pos hqw]
      exact hcap q ⟨le_of_not_ge hqh,hqw⟩
    · rw [if_neg hqw]
      exact flatNumerator_forward_nonpos (by norm_num : (0:ℝ)≤13/20) hE hslack
        ⟨le_of_not_ge hqw,hq.2⟩ hn.left hn.right hn.kink

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

theorem largeSelected_fixedMass_of_signs (h : VerifierCurve phi lam)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    {z q : ℝ} (hz : z∈Icc (391/500:ℝ) (7/8)) (hq : q∈Icc (0:ℝ) lam)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hn : LargeSelectedRankSigns lam S z) :
    largeSelectedNumerator lam S z q (cubic lam S z)
      (largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S)) (13/20)≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hprod : lam*S≤3/200 := by
    have hh := mul_le_mul hL.2 hS.2 (by linarith only [hS.1]) (by norm_num : (0:ℝ)≤56233/100000)
    norm_num at hh ⊢
    linarith only [hh]
  have hslack : 0<capSlack lam S (1459/5000) := by
    have hh := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
      (by linarith only [hL.1] : 0≤lam)
    norm_num [capSlack,capScore]
    nlinarith only [hh,hL.1]
  have hE : 0≤capDeficit lam S (1459/5000) := by
    have hh := h.primitive_relative_quadratic_antitone
      (a:=1459/5000) (by norm_num) (b:=31/40) (by norm_num) (by norm_num)
    dsimp only at hh
    rw [g.cap_primitive (1459/5000) ⟨by norm_num,g.contact_mem.1⟩,
      g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
    unfold capDeficit
    linarith only [hh]
  exact largeSelected_fixedMass_nonpos hz hq (by linarith only [g.head_slope])
    hprod hE hslack hcapOrder hn

end BinaryCurveGeometry
end OptimalG
