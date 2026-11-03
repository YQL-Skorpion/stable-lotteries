import OptimalG.VariationalLinearCoercivity
import OptimalG.VariationalMatchingDeficits
import OptimalG.VariationalDeficitRational

/-! Rational consequences of relaxed upper-reference transport constants.
Every numerical premise is explicit; the reference-cell checks supply these
constants before this module is used for the minimizing curve. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem upper_transport_localization {initial A ds k eb V : ℝ}
    (hi : 0 ≤ initial) (hA : |A|≤(0.00011:ℝ))
    (hk : k≤-(16:ℝ)) (heb : eb≤0) (hV : 0≤V)
    (hbound : initial+A*ds+54*ds^2+k*eb+0.64*V≤(0.000003:ℝ)) :
    |ds|<(0.000237:ℝ) ∧ V<(0.000004688:ℝ) ∧
      -eb<(0.000000188:ℝ) ∧ initial≤(0.0000030001:ℝ) := by
  have hkeb := mul_nonneg_of_nonpos_of_nonpos (show k≤0 by linarith) heb
  have hgap := mul_nonneg (by norm_num : (0:ℝ)≤0.64) hV
  have hscalar : 54*ds^2+A*ds≤(0.000003:ℝ) := by linarith
  have hs := transport_scalar_radius (by norm_num : (0:ℝ)<54) hA
    (by norm_num : (0:ℝ)≤0.000237) (by norm_num) (by norm_num) hscalar
  have haux := transport_auxiliary_budget (by norm_num : (0:ℝ)<54) hA hbound
  have haux' : initial+k*eb+0.64*V≤(0.0000030001:ℝ) := by
    norm_num at haux
    linarith only [haux]
  have hboundary := mul_le_mul_of_nonpos_right hk heb
  refine ⟨hs,?_,?_,?_⟩ <;> linarith

theorem upper_transport_scalar_tube {S delta : ℝ}
    (hd : delta∈Icc (0:ℝ) 0.000005)
    (hS : |(S+0.2012*delta)-(2303623505254907/100000000000000000:ℝ)|<(0.000237:ℝ)) :
    S∈Icc (0.02271790:ℝ) 0.023354 := by
  have hh := abs_lt.mp hS
  constructor <;> linarith only [hh.1,hh.2,hd.1,hd.2]

theorem upper_transport_initial_primitive {a b : ℝ} {J Xi : ℝ → ℝ}
    (G : StieltjesFunction ℝ) (hab : a≤b) (hleft : Function.leftLim G a=a)
    (hJ : LipschitzOnWith (1/3:NNReal) J (Icc a b))
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧ J (G r)=Xi r)
    (hV : matchingVariation G a b<(0.000004688:ℝ)) :
    Xi a-J a<(0.000001563:ℝ) := by
  have hh := matching_initial_primitive_deficit G hab hleft hJ hmatch
  norm_num at hh
  linarith only [hh,hV]

theorem upper_transport_terminal_primitive {a b : ℝ} {J Xi G : ℝ → ℝ}
    (hab : a≤b) (hJ : LipschitzOnWith (1/3:NNReal) J (Icc a b))
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧ J (G r)=Xi r)
    (heb : b-G b<(0.000000188:ℝ)) :
    J b-Xi b<(0.000000063:ℝ) := by
  have hh := matching_terminal_primitive_deficit hab hJ hmatch
  norm_num at hh
  linarith only [hh,heb]

end OptimalG.Variational
