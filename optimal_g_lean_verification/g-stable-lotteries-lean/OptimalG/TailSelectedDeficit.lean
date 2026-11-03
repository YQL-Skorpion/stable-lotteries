import OptimalG.TailReanchor
import OptimalG.BinarySmallCentral

/-! The fixed-anchor tail box supplies the actual primitive-deficit bound
needed for the extended-mass selected-high argument. -/
namespace OptimalG
open Set Variational

theorem tail_selected_deficit_scalar {lam S Y H : ℝ}
    (hL : lam≤56233/100000) (hS : 227179/10000000≤S)
    (hY : 8793/100000≤Y) (hH : -(3589/10000)≤H) :
    quadratic lam (7/8)-S-tailPrimitive (539/625) Y H (7/8)<17/5000 := by
  have hm := tailPrimitive_mono_anchor
    (a:=539/625) (r:=7/8) (by norm_num) (by norm_num) hY hH
  have hbase : quadratic (56233/100000) (7/8)-(227179/10000000)-
      tailPrimitive (539/625) (8793/100000) (-(3589/10000)) (7/8)<17/5000 := by
    norm_num [quadratic,tailPrimitive,tailCoord,tailOne,tailTwo]
  unfold quadratic at *
  linarith only [hL,hS,hm,hbase]

/-- A single actual primitive value at .875 and the score ceiling cover the
whole preceding high interval. The anchor values may be extrapolations. -/
theorem VerifierCurve.selected_deficit_bound {phi : ℝ→ℝ} {lam S Y H : ℝ}
    (h : VerifierCurve phi lam)
    (hL : lam≤56233/100000) (hS : 227179/10000000≤S)
    (hY : 8793/100000≤Y) (hH : -(3589/10000)≤H)
    (hstart : curvePrimitive phi (9/25)=quadratic lam (9/25)-S)
    (hfinish : curvePrimitive phi (7/8)=tailPrimitive (539/625) Y H (7/8)) :
    ∀ r∈Icc (9/25:ℝ) (7/8),primitiveDefect phi lam S r∈Icc (0:ℝ) (17/5000) := by
  intro r hr
  have hr01 : r∈Icc (0:ℝ) 1 := ⟨by linarith only [hr.1],by linarith only [hr.2]⟩
  have hlow := h.primitive_relative_quadratic_antitone
    (a:=9/25) (by norm_num) hr01 hr.1
  have hhigh := h.primitive_relative_quadratic_antitone
    hr01 (b:=7/8) (by norm_num) hr.2
  dsimp only at hlow hhigh
  rw [hstart] at hlow
  rw [hfinish] at hhigh
  have hbound := tail_selected_deficit_scalar hL hS hY hH
  unfold primitiveDefect
  constructor <;> linarith only [hlow,hhigh,hbound]

end OptimalG
