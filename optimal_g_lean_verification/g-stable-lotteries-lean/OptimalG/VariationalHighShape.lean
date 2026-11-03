import OptimalG.HighContinuationShape
import OptimalG.VariationalFeatureBounds

/-! Application of the derivative-free concavity argument to the actual
essential-support controls. Only the numerical active-coefficient bound is
left as input; support attainment and primitive regularity are proved here. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def featureAlpha (lam : ℝ) (d : LowRankData) (v : ControlFeature) : ℝ :=
  Certificates.Control.alphaNumerator (2*lam-v.1.2.1) (v.1.1+v.1.2.2-lam) v.2.1 v.2.2 /
    controlDeterminant lam d v.1

theorem featureH_as_highAffineControl {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) (Y : ℝ → ℝ) (r : ℝ) :
    featureH hd r (Y r) v=
      highAffineControl lam d.S v.1.1 (featureTheta lam d v) (featureAlpha lam d v) Y r := by
  rw [featureH_eq_value hd r (Y r) v.2.1 v.2.2 (hd.controlFeatureSupport_subset hv).1]
  unfold highAffineControl featureTheta featureAlpha Certificates.Control.value
    Certificates.Control.theta controlDeterminant Certificates.Control.det
  ring

theorem featureAlpha_nonneg_of_coefficient {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hc : 1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1) :
    0 ≤ featureAlpha lam d v := by
  have ht := (hd.featureTheta_bounds hv).2
  have hp := (hd.controlFeatureSupport_subset hv).1.1.1
  have hp0 : 0 < v.1.1 := by norm_num [pLo] at hp; linarith
  exact (nonneg_of_mul_nonneg_left (by linarith : 0 ≤ featureAlpha lam d v*v.1.1) hp0)

/-- The only additional premise is a bound on genuinely active support controls. -/
theorem continuation_score_concave {lam a b : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : zStart ≤ a) (hb : b ≤ zEnd)
    (hactive : ∀ r ∈ Icc a b,∀ v ∈ controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r) ≠ lam-r →
      1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1) :
    (∀ x ∈ Icc a b,∀ y ∈ Icc a b,x ≤ y →
      vectorField lam d y (Y y)-vectorField lam d x (Y x) ≤ x-y) ∧
    ConcaveOn ℝ (Icc a b) (fun r => vectorField lam d r (Y r)) := by
  let Good : Set ControlFeature := {v | v ∈ controlFeatureSupport d ∧
    1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1}
  let mass : Good → ℝ := fun v => v.1.1.1
  let theta : Good → ℝ := fun v => featureTheta lam d v.1
  let alpha : Good → ℝ := fun v => featureAlpha lam d v.1
  have hs : Icc a b ⊆ Icc zStart zEnd := Icc_subset_Icc ha hb
  apply highContinuation_concave (p := mass) (theta := theta) (alpha := alpha)
    (S := d.S) ((continuation_continuous hY).mono hs)
  · intro r hr
    exact (hY.2 r (hs ⟨hr.1.le,hr.2.le⟩)).hasDerivAt
      (Icc_mem_nhds (ha.trans_lt hr.1) (hr.2.trans_le hb))
  · intro v
    exact ⟨featureAlpha_nonneg_of_coefficient hd v.2.1 v.2.2,v.2.2⟩
  · intro r hr
    refine ⟨vectorField_le_line lam d r (Y r),?_⟩
    intro v
    change _ ≤ highAffineControl lam d.S v.1.1.1 (featureTheta lam d v.1)
      (featureAlpha lam d v.1) Y r
    rw [← featureH_as_highAffineControl hd v.2.1]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH r (Y r) v.2.1)
  · intro r hr
    by_cases he : vectorField lam d r (Y r)=lam-r
    · exact Or.inl he
    · right
      have hess : vectorField lam d r (Y r)=essInf (controlH lam d r (Y r)) controlMeasure := by
        rcases min_choice (lam-r) (essInf (controlH lam d r (Y r)) controlMeasure) with h | h
        · exact False.elim (he h)
        · exact h
      obtain ⟨v,hv,hval⟩ := hd.essInf_attained_in_featureSupport r (Y r)
      have hvf : featureH hd r (Y r) v=vectorField lam d r (Y r) := hval.trans hess.symm
      let w : Good := ⟨v,hv,hactive r hr v hv hvf he⟩
      refine ⟨w,?_⟩
      change _=highAffineControl lam d.S v.1.1 (featureTheta lam d v) (featureAlpha lam d v) Y r
      rw [← featureH_as_highAffineControl hd hv]
      exact hvf.symm

end OptimalG.Variational
