import OptimalG.DeficitQuadraticGrowth
import OptimalG.VerifierPrimitiveCap
import OptimalG.Certificates.LargeTailExpressions
import OptimalG.BinaryCurveGeometry

namespace OptimalG
open Set Variational

noncomputable def largeTailMassFloor (lam S p : ℝ) : ℝ :=
  if p≤391/500 then Certificates.LargeTailExpressions.massCap lam S p
  else Certificates.LargeTailExpressions.massLower lam S p

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem largeTail_mass_box {S p Y H : ℝ}
    (hconc : ConcaveOn ℝ (Icc lam 1) phi)
    (hL : lam≤56233/100000) (hS : 227179/10000000≤S)
    (hY : 8793/100000≤Y) (hH : -(3589/10000)≤H)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hanchor : curvePrimitive phi (9/25)=quadratic lam (9/25)-S)
    (hfinish : curvePrimitive phi (7/8)=tailPrimitive (539/625) Y H (7/8))
    (hp : p∈Icc (13/20:ℝ) (41/50)) :
    curvePrimitive phi p∈Icc (largeTailMassFloor lam S p)
      (Certificates.LargeTailExpressions.massCap lam S p) := by
  have hlineJ := h.primitive_eq_quadratic_on_line
    (show (0:ℝ)≤9/25 by norm_num) (show (9/25:ℝ)≤391/500 by norm_num)
    (show (391/500:ℝ)≤1 by norm_num) hanchor hline
  by_cases hpl : p≤391/500
  · have hj := hlineJ p ⟨by linarith only [hp.1],hpl⟩
    rw [largeTailMassFloor,if_pos hpl,hj]
    exact ⟨le_rfl,le_rfl⟩
  · have hd := h.selected_deficit_bound hL hS hY hH hanchor hfinish
    have hdp := hd p ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
    have hdb := hd (7/8) ⟨by norm_num,le_rfl⟩
    have hg := h.high_deficit_quadratic_bound hconc (by linarith only [hL])
      ⟨le_of_not_ge hpl,by linarith only [hp.2]⟩
      (hlineJ (391/500) ⟨by norm_num,le_rfl⟩)
      (hline (391/500) ⟨by norm_num,le_rfl⟩) hdb.2
    rw [largeTailMassFloor,if_neg hpl]
    unfold primitiveDefect at hdp hg
    unfold Certificates.LargeTailExpressions.massLower Certificates.LargeTailExpressions.massCap
    constructor <;> linarith only [hdp.1,hg]

end VerifierCurve

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

theorem largeTail_scalar_inputs (h : VerifierCurve phi lam)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    0<1+slope ∧ lam*S≤3/200 ∧ 0≤capDeficit lam S (1459/5000) ∧
      0<capSlack lam S (1459/5000) := by
  have hs : 0<1+slope := by linarith only [g.head_slope]
  have hp : lam*S≤3/200 := by
    have hh := mul_le_mul
      (show lam≤3/5 by linarith only [g.lambda_mem.2])
      (show S≤1/40 by linarith only [hS.2])
      (show 0≤S by linarith only [hS.1]) (show (0:ℝ)≤3/5 by norm_num)
    norm_num at hh
    exact hh
  have he : 0≤capDeficit lam S (1459/5000) := by
    have hh := h.primitive_relative_quadratic_antitone
      (a:=1459/5000) (by constructor <;> norm_num)
      (b:=9/25) (by constructor <;> norm_num) (by norm_num)
    dsimp only at hh
    rw [g.cap_primitive (1459/5000) ⟨by norm_num,g.contact_mem.1⟩,
      g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩] at hh
    unfold capDeficit
    linarith only [hh]
  have hg : 0<capSlack lam S (1459/5000) := by
    have hmul := mul_le_mul g.lambda_mem.1 hS.1
      (show (0:ℝ)≤227179/10000000 by norm_num)
      (show 0≤lam by linarith only [g.lambda_mem.1])
    norm_num [capSlack,capScore]
    nlinarith only [g.lambda_mem.1,hmul]
  exact ⟨hs,hp,he,hg⟩

end BinaryCurveGeometry
end OptimalG
