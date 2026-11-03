import OptimalG.Certificates.SmallMassExpressions
import OptimalG.VariationalReferenceGrowth

/-! The cap-versus-head slope order follows from the parameter rectangle.
No recovered curve or extra numerical certificate is needed. -/
namespace OptimalG
open Set Variational

 theorem smallMass_head_slope_le_neg_half {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    Certificates.SmallMassExpressions.slope lam S≤ -(1/2:ℝ) := by
  have hLS := mul_le_mul hL.2 hS.2 (by linarith only [hS.1] : 0≤S)
    (by norm_num : (0:ℝ)≤56233/100000)
  have hsq : (22493/40000:ℝ)^2≤lam^2 := pow_le_pow_left₀ (by norm_num) hL.1 2
  unfold Certificates.SmallMassExpressions.slope headSlope headInitial cap capScore
  norm_num
  nlinarith only [hL.1,hL.2,hLS,hsq]

 theorem capScore_curvature_ge_neg_half {lam S r : ℝ}
    (hprod : lam*S≤3/200) (hr : r≤9/25) :
    -(1/2:ℝ)≤ -2*lam*S/(1-r)^3 := by
  have hp : (16/25:ℝ)^3≤(1-r)^3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith only [hr]) 3
  apply (le_div_iff₀ (pow_pos (by linarith only [hr] : 0<1-r) 3)).mpr
  nlinarith only [hprod,hp]

 theorem capScore_increment_ge_neg_half {lam S u v : ℝ}
    (hprod : lam*S≤3/200) (huv : u≤v) (hv : v≤9/25) :
    -(1/2:ℝ)*(v-u)≤capScore lam S v-capScore lam S u := by
  exact reference_primitive_lower_increment (a:=u) (b:=v) (m0:= -(1/2:ℝ))
    (fun r hr => capScore_hasDerivAt lam S r (by linarith only [hr.2,hv]))
    (fun r hr => capScore_curvature_ge_neg_half hprod (hr.2.le.trans hv))
    u ⟨le_rfl,huv⟩ v ⟨huv,le_rfl⟩ huv

/-- Rectangle-only form of the cap-order premise in the C.4/C.5 reductions.
The lower endpoint need not be nonnegative. -/
 theorem capScore_increment_ge_headSlope {lam S u v : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (huv : u≤v) (hv : v≤9/25) :
    Certificates.SmallMassExpressions.slope lam S*(v-u)≤
      capScore lam S v-capScore lam S u := by
  have hLS := mul_le_mul hL.2 hS.2 (by linarith only [hS.1] : 0≤S)
    (by norm_num : (0:ℝ)≤56233/100000)
  have hp : lam*S≤3/200 := by norm_num at hLS ⊢; linarith only [hLS]
  exact (mul_le_mul_of_nonneg_right (smallMass_head_slope_le_neg_half hL hS)
    (sub_nonneg.mpr huv)).trans (capScore_increment_ge_neg_half hp huv hv)

 theorem capHeadSlopeOrder {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤
        capScore lam S v-capScore lam S u := by
  intro u _ v hv huv
  exact capScore_increment_ge_headSlope hL hS huv hv.2

end OptimalG
