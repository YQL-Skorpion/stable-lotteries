import OptimalG.VariationalIntegratingFactor

/-! An actual absolutely continuous reference trajectory for arbitrary
integrable scalar affine coefficients. Piecewise reference controls therefore
require no unproved ODE existence assumption at their join points. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Real
open scoped Topology

noncomputable def affineReferenceSolution (a x0 : ℝ) (alpha beta : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (∫ s in a..t,alpha s) *
    (x0+∫ s in a..t, exp (-(∫ r in a..s,alpha r))*beta s)

 theorem affineReferenceSolution_initial (a x0 : ℝ) (alpha beta : ℝ → ℝ) :
    affineReferenceSolution a x0 alpha beta a = x0 := by
  simp [affineReferenceSolution]

 theorem affineReferenceSolution_AC {a b x0 : ℝ} {alpha beta : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b) (hb : IntervalIntegrable beta volume a b) :
    AbsolutelyContinuousOnInterval (affineReferenceSolution a x0 alpha beta) a b := by
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hE := absolutelyContinuous_exp hA
  have hEm := absolutelyContinuous_exp hA.neg
  have hi : IntervalIntegrable (fun s => exp (-(∫ r in a..s,alpha r))*beta s) volume a b :=
    hb.continuousOn_mul hEm.continuousOn
  have hI := hi.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => x0) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hE.mul (hc.add hI)

 theorem affineReferenceSolution_hasDerivAt_ae {a b x0 : ℝ} {alpha beta : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b) (hb : IntervalIntegrable beta volume a b) :
    ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (affineReferenceSolution a x0 alpha beta)
        (alpha t*affineReferenceSolution a x0 alpha beta t+beta t) t := by
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral (show a ∈ uIcc a b by simp)
  have hEm := absolutelyContinuous_exp hA.neg
  have hi : IntervalIntegrable (fun s => exp (-(∫ r in a..s,alpha r))*beta s) volume a b :=
    hb.continuousOn_mul hEm.continuousOn
  filter_upwards [ha.ae_hasDerivAt_integral,hi.ae_hasDerivAt_integral] with t hat hit ht
  have h := (hat ht a (by simp)).exp.mul ((hit ht a (by simp)).const_add x0)
  convert! h using 1
  dsimp [affineReferenceSolution]
  have he : exp (∫ s in a..t,alpha s)*exp (-(∫ s in a..t,alpha s)) = 1 := by
    rw [← exp_add,add_neg_cancel,exp_zero]
  have he' := congrArg (fun q : ℝ => q*beta t) he
  simp only [one_mul] at he'
  nlinarith only [he']

 theorem exists_affine_reference_solution {a b x0 : ℝ} {alpha beta : ℝ → ℝ}
    (ha : IntervalIntegrable alpha volume a b) (hb : IntervalIntegrable beta volume a b) :
    ∃ Z : ℝ → ℝ, Z a=x0 ∧ AbsolutelyContinuousOnInterval Z a b ∧
      ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt Z (alpha t*Z t+beta t) t :=
  ⟨affineReferenceSolution a x0 alpha beta,affineReferenceSolution_initial _ _ _ _,
    affineReferenceSolution_AC ha hb,affineReferenceSolution_hasDerivAt_ae ha hb⟩

end OptimalG.Variational
