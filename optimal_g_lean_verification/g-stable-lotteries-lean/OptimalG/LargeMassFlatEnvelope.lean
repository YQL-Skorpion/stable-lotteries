import OptimalG.ExtendedSlackProfiles

/-! A continuous coarse upper envelope is sufficient for large-mass mixed
tests. Its constant remaining-area tail removes a jump at the line boundary. -/
namespace OptimalG
open Set Variational

noncomputable def largeRemainingUpper (lam S F slope r : ℝ) : ℝ :=
  if r≤527/2000 then F*r+slope*r^2/2-quadratic lam r+S
  else if r≤313/1000 then capDeficit lam S r
  else capDeficit lam S (313/1000)

noncomputable def largeRemainingLower (lam S F slope q : ℝ) : ℝ :=
  if q≤527/2000 then F*q+slope*q^2/2-quadratic lam q+S
  else if q≤1459/5000 then capDeficit lam S q
  else max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000))

noncomputable def largePrimitiveUpper (lam S F slope r : ℝ) : ℝ :=
  quadratic lam r-S+largeRemainingUpper lam S F slope r

theorem largeRemainingLower_eq (lam S F slope q : ℝ) :
    largeRemainingLower lam S F slope q=
      S-extendedSlackUpper lam S F slope (527/2000) (1459/5000) q := by
  unfold largeRemainingLower extendedSlackUpper
  simp only [capDeficit]
  split_ifs <;> ring

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

theorem largeRemainingUpper_bound (h : VerifierCurve phi lam) {r : ℝ}
    (hr : r∈Icc (0:ℝ) 1) :
    binarySlackArea phi lam S r≤largeRemainingUpper lam S (phi 0) slope r := by
  have hcap {q : ℝ} (hq : q∈Icc (0:ℝ) (53/100)) :
      binarySlackArea phi lam S q≤capDeficit lam S q := by
    have hh := g.cap_upper q hq
    unfold binarySlackArea capDeficit
    linarith only [hh]
  by_cases hh : r≤527/2000
  · rw [largeRemainingUpper,if_pos hh,binarySlackArea,
      h.affine_head_primitive g.head ⟨hr.1,hh⟩]
  · by_cases hcut : r≤313/1000
    · rw [largeRemainingUpper,if_neg hh,if_pos hcut]
      exact hcap ⟨hr.1,by linarith only [hcut]⟩
    · rw [largeRemainingUpper,if_neg hh,if_neg hcut]
      exact (h.binarySlackArea_antitone S
        (show (313/1000:ℝ)∈Icc 0 1 by constructor <;> norm_num) hr
        (le_of_not_ge hcut)).trans (hcap (by constructor <;> norm_num))

theorem largeRemainingLower_bound (h : VerifierCurve phi lam) {q : ℝ}
    (hq : q∈Icc (0:ℝ) lam) :
    largeRemainingLower lam S (phi 0) slope q≤binarySlackArea phi lam S q := by
  have hh := g.slackUpper_bound h hq
  rw [largeRemainingLower_eq]
  unfold binarySlackArea
  linarith only [hh]

theorem largePrimitiveUpper_bound (h : VerifierCurve phi lam) {r : ℝ}
    (hr : r∈Icc (0:ℝ) 1) :
    curvePrimitive phi r≤largePrimitiveUpper lam S (phi 0) slope r := by
  have hh := g.largeRemainingUpper_bound h hr
  unfold largePrimitiveUpper binarySlackArea at *
  linarith only [hh]

theorem largePrimitiveUpper_head (h : VerifierCurve phi lam) {q : ℝ}
    (hq : q∈Icc (0:ℝ) (527/2000)) :
    largePrimitiveUpper lam S (phi 0) slope q=curvePrimitive phi q := by
  rw [largePrimitiveUpper,largeRemainingUpper,if_pos hq.2,h.affine_head_primitive g.head hq]
  ring

end BinaryCurveGeometry
end OptimalG
