import OptimalG.VariationalMeasuredMatching

/-! Positive reference score implies all increment and inverse bounds used
by the actual matching construction. -/
namespace OptimalG.Variational
open Set MeasureTheory Function
open scoped NNReal

 theorem reference_primitive_lower_increment {a b m0 : ℝ} {Xi m : ℝ → ℝ}
    (hXi : ∀ r ∈ Icc a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, m0 ≤ m r) :
    ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → m0*(s-r) ≤ Xi s-Xi r := by
  let g := fun r => Xi r-m0*r
  have hgd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt g (m r-m0) r := by
    convert! (hXi r hr).sub ((hasDerivAt_id r).const_mul m0) using 1 <;> simp [g]
  have hmono : MonotoneOn g (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun r hr => (hgd r hr).continuousAt.continuousWithinAt)
    · intro r hr
      exact (hgd r (interior_subset hr)).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact sub_nonneg.mpr (hm r hr)
  intro r hr s hs hrs
  have h := hmono hr hs hrs
  dsimp [g] at h
  nlinarith only [h]

 theorem reference_primitive_strictMono {a b m0 : ℝ} {Xi m : ℝ → ℝ}
    (hm0 : 0 < m0) (hXi : ∀ r ∈ Icc a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, m0 ≤ m r) : StrictMonoOn Xi (Icc a b) := by
  intro r hr s hs hrs
  have h := reference_primitive_lower_increment hXi hm r hr s hs hrs.le
  have hp := mul_pos hm0 (sub_pos.mpr hrs)
  linarith

 theorem exists_measured_primitive_matching_of_deriv {a b m0 : ℝ} {M : ℝ≥0}
    {J Xi phi m : ℝ → ℝ}
    (hab : a ≤ b) (hm0 : 0 < m0) (hM : 0 < (M:ℝ))
    (hJmono : MonotoneOn J (Icc a b)) (hJlip : LipschitzOnWith M J (Icc a b))
    (hleft : J a ≤ Xi a) (hright : Xi b ≤ J b)
    (hJd : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt J (phi s) s ∧ 0 ≤ phi s ∧ phi s ≤ M)
    (hXid : ∀ r ∈ Icc a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, m0 ≤ m r) :
    ∃ G : StieltjesFunction ℝ, leftLim G a = a ∧
      (∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r) = Xi r) ∧
      (∀ᵐ r ∂volume.restrict (Icc a b), HasDerivAt G (deriv G r) r ∧
        0 < deriv G r ∧ m0/(M:ℝ) ≤ deriv G r ∧ phi (G r) = m r/deriv G r) ∧
      ∀ r ∈ Icc a b, (G r-r)^2 ≤ 2*(b-a)*matchingVariation G a b := by
  exact exists_measured_primitive_matching hab hm0 hM hJmono hJlip
    (fun r hr => (hXid r hr).continuousAt.continuousWithinAt)
    (reference_primitive_strictMono hm0 hXid hm)
    (reference_primitive_lower_increment hXid hm) hleft hright hJd
    (fun r hr => hXid r ⟨hr.1.le,hr.2.le⟩) hm

end OptimalG.Variational
