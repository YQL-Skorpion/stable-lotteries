import OptimalG.LargeMassFlatEnvelope
import OptimalG.Certificates.SmallMassExpressions
import OptimalG.VerifierPrimitiveCap

namespace OptimalG
open Set Variational

theorem largeSelected_capSlack_upper {lam S r : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hr : r∈Icc (527/2000:ℝ) (313/1000)) : capSlack lam S r≤1/20 := by
  have hprod := mul_le_mul
    (show lam≤3/5 by linarith only [hL.2]) (show S≤1/40 by linarith only [hS.2])
    (show 0≤S by linarith only [hS.1]) (show (0:ℝ)≤3/5 by norm_num)
  have hd : (687/1000:ℝ)^2≤(1-r)^2 := by
    nlinarith only [hr.2,sq_nonneg (r-313/1000)]
  have hd0 : 0<(1-r)^2 := pow_pos (by linarith only [hr.2]) 2
  have hf : lam*S/(1-r)^2≤4/125 := by
    rw [div_le_iff₀ hd0]
    nlinarith only [hprod,hd]
  unfold capSlack capScore
  linarith only [hf,hL.2,hr.1]

theorem largeSelected_capDeficit_le_area {lam S r : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hr : r∈Icc (527/2000:ℝ) (313/1000)) : capDeficit lam S r≤S := by
  have hL0 : 0≤lam := by linarith only [hL.1]
  have hS0 : 0≤S := by linarith only [hS.1]
  have hr0 : 0≤r := by linarith only [hr.1]
  have hLS := mul_le_mul (show (281/500:ℝ)≤lam by linarith only [hL.1])
    (show (1/50:ℝ)≤S by linarith only [hS.1]) (by norm_num : (0:ℝ)≤1/50) hL0
  have hLr := mul_le_mul (show (281/500:ℝ)≤lam by linarith only [hL.1])
    hr.1 (by norm_num : (0:ℝ)≤527/2000) hL0
  have hLsq := mul_le_mul (show lam≤563/1000 by linarith only [hL.2])
    (show lam≤563/1000 by linarith only [hL.2]) hL0 (by norm_num : (0:ℝ)≤563/1000)
  have hrsq := mul_le_mul hr.2 hr.2 hr0 (by norm_num : (0:ℝ)≤313/1000)
  have hd : 0<1-r := by linarith only [hr.2]
  have hself : lam*S≤lam*S/(1-r) := by
    rw [le_div_iff₀ hd]
    have hm := mul_nonneg (mul_nonneg hL0 hS0) hr0
    nlinarith only [hm]
  unfold capDeficit cap quadratic
  nlinarith only [hLS,hLr,hLsq,hrsq,hself,hL.1]

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

theorem largeSelected_initial_gap
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S) :
    1/20≤lam-Certificates.SmallMassExpressions.initial lam S := by
  have hh := g.head (527/2000) ⟨by norm_num,le_rfl⟩
  have hc := g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  rw [hi] at hh
  have hp : 0≤lam*S/(1-(527/2000:ℝ))^2 := by
    apply div_nonneg
    · exact mul_nonneg (by linarith only [g.lambda_mem.1]) (by linarith only [hS.1])
    · positivity
  unfold capScore at hc
  nlinarith only [hh,hc,hp,g.lambda_mem.1,g.head_slope]

theorem largeSelected_upper_le_area (h : VerifierCurve phi lam)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) r≤S := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  by_cases hhead : r≤527/2000
  · rw [largeRemainingUpper,if_pos hhead]
    have hj := h.affine_head_primitive g.head ⟨hr.1,hhead⟩
    rw [hi] at hj
    have hu := h.primitive_le_quadratic_after_anchor (a:=0) (S:=0)
      ⟨le_rfl,by norm_num⟩ (by simp [curvePrimitive,quadratic]) r hr
    linarith only [hj,hu]
  · by_cases hcap : r≤313/1000
    · rw [largeRemainingUpper,if_neg hhead,if_pos hcap]
      exact largeSelected_capDeficit_le_area hL hS ⟨le_of_not_ge hhead,hcap⟩
    · rw [largeRemainingUpper,if_neg hhead,if_neg hcap]
      exact largeSelected_capDeficit_le_area hL hS ⟨by norm_num,le_rfl⟩

theorem largeSelected_lower_nonneg (h : VerifierCurve phi lam)
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S)
    {q : ℝ} (hq : q∈Icc (0:ℝ) lam) :
    0≤largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) q := by
  have hlow (t : ℝ) (ht : t∈Icc (0:ℝ) (9/25)) :
      0≤curvePrimitive phi t-quadratic lam t+S := by
    have hh := h.primitive_relative_quadratic_antitone
      ⟨ht.1,by linarith only [ht.2]⟩ (show (9/25:ℝ)∈Icc 0 1 by constructor <;> norm_num) ht.2
    dsimp only at hh
    rw [g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩] at hh
    linarith only [hh]
  by_cases hhead : q≤527/2000
  · rw [largeRemainingLower,if_pos hhead]
    have hh := hlow q ⟨hq.1,by linarith only [hhead]⟩
    rw [h.affine_head_primitive g.head ⟨hq.1,hhead⟩,hi] at hh
    exact hh
  · by_cases hcap : q≤1459/5000
    · rw [largeRemainingLower,if_neg hhead,if_pos hcap]
      have hh := hlow q ⟨hq.1,by linarith only [hcap]⟩
      rw [g.cap_primitive q ⟨le_of_not_ge hhead,hcap.trans g.contact_mem.1⟩] at hh
      unfold capDeficit
      linarith only [hh]
    · rw [largeRemainingLower,if_neg hhead,if_neg hcap]
      exact le_max_left _ _

end BinaryCurveGeometry
end OptimalG
