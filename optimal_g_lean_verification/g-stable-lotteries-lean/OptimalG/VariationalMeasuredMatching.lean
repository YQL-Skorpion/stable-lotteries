import OptimalG.VariationalMatchedDerivative
import OptimalG.VariationalTransportLocalization

/-! A complete equal-primitive matching: actual construction, right
continuity, singular mass, derivative identity, and quantitative displacement. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Function
open scoped NNReal

 theorem exists_measured_primitive_matching {a b m0 : ℝ} {M : ℝ≥0}
    {J Xi phi m : ℝ → ℝ}
    (hab : a ≤ b) (hm0 : 0 < m0) (hM : 0 < (M:ℝ))
    (hJmono : MonotoneOn J (Icc a b)) (hJlip : LipschitzOnWith M J (Icc a b))
    (hXi : ContinuousOn Xi (Icc a b)) (hXimono : StrictMonoOn Xi (Icc a b))
    (hgrowth : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → m0*(s-r) ≤ Xi s-Xi r)
    (hleft : J a ≤ Xi a) (hright : Xi b ≤ J b)
    (hJd : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt J (phi s) s ∧ 0 ≤ phi s ∧ phi s ≤ M)
    (hXid : ∀ r ∈ Ioo a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, m0 ≤ m r) :
    ∃ G : StieltjesFunction ℝ, leftLim G a = a ∧
      (∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r) = Xi r) ∧
      (∀ᵐ r ∂volume.restrict (Icc a b), HasDerivAt G (deriv G r) r ∧
        0 < deriv G r ∧ m0/(M:ℝ) ≤ deriv G r ∧ phi (G r) = m r/deriv G r) ∧
      ∀ r ∈ Icc a b, (G r-r)^2 ≤ 2*(b-a)*matchingVariation G a b := by
  obtain ⟨G,hGa,hmatch⟩ := exists_stieltjes_primitive_matching hab hJlip.continuousOn hJmono
    hXi hXimono hleft hright
  have hstrict := primitive_matching_strictMono hJmono hXimono hmatch
  have hgrow := primitive_matching_growth hJmono hJlip hXimono hgrowth hmatch
  let K : ℝ≥0 := ⟨(M:ℝ)/m0,div_nonneg M.coe_nonneg hm0.le⟩
  have hinverse : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, dist r s ≤ (K:ℝ)*dist (G r) (G s) :=
    primitive_matching_inverse_bound hm0 hstrict.monotoneOn hgrow
  have hjbasic : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt J (phi s) s ∧ 0 ≤ phi s := by
    filter_upwards [hJd] with s hs hsi
    exact ⟨(hs hsi).1,(hs hsi).2.1⟩
  have hder := matched_rank_derivative hstrict.monotoneOn hstrict.injOn hinverse hmatch hjbasic
    hXid (fun r hr => hm0.trans_le (hm r hr))
  have hpull := ae_pullback_of_inverse_lipschitz measurableSet_Icc hstrict.injOn hinverse hJd
  have hfull : ∀ᵐ r ∂volume.restrict (Icc a b), HasDerivAt G (deriv G r) r ∧
      0 < deriv G r ∧ m0/(M:ℝ) ≤ deriv G r ∧ phi (G r) = m r/deriv G r := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hder,ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hpull] with r hdr hr hj
    have hj' := hj (hmatch r ⟨hr.1.le,hr.2.le⟩).1
    refine ⟨hdr.1,hdr.2.1,?_,hdr.2.2⟩
    apply (div_le_iff₀ hM).2
    have he : phi (G r)*deriv G r = m r := (eq_div_iff hdr.2.1.ne').1 hdr.2.2
    have hu := mul_le_mul_of_nonneg_right hj'.2.2 hdr.2.1.le
    nlinarith only [he,hu,hm r hr]
  refine ⟨G,hGa,hmatch,hfull,?_⟩
  intro r hr
  exact stieltjes_displacement_sq_bound G hab hGa (hmatch b ⟨hab,le_rfl⟩).1.2
    (hfull.mono (fun _ h => h.2.1)) hr

end OptimalG.Variational
