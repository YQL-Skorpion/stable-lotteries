import OptimalG.VariationalTransportLocalization
import OptimalG.VariationalCompactness

/-! Actual low-rank deficit bounds extracted from the matching. The left
endpoint uses the retained initial singular atom; the right endpoint uses the
terminal boundary term, rather than the weaker square-displacement bound. -/
namespace OptimalG.Variational
open Set MeasureTheory Function
open scoped NNReal

 theorem stieltjes_singular_singleton (G : StieltjesFunction ℝ) (a : ℝ) :
    (G.measure.singularPart volume) {a}=G.measure {a} := by
  have h := congrArg (fun mu : Measure ℝ => mu {a}) (G.measure.rnDeriv_add_singularPart volume)
  have hz : (volume.withDensity (G.measure.rnDeriv volume)) {a}=0 := by
    exact withDensity_absolutelyContinuous _ _ (by simp)
  simpa only [Measure.add_apply,hz,zero_add] using h

 theorem matching_initial_atom_le_variation (G : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a ≤ b) (hleft : leftLim G a=a) : G a-a ≤ matchingVariation G a b := by
  have hGa : a ≤ G a := calc
    a = leftLim G a := hleft.symm
    _ ≤ G a := G.mono.leftLim_le le_rfl
  have hatom : (G.measure.singularPart volume).real {a}=G a-a := by
    rw [measureReal_def,stieltjes_singular_singleton,G.measure_singleton,hleft,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hGa)]
  have hsing : (G.measure.singularPart volume) (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top isCompact_Icc.measure_lt_top.ne (G.measure.singularPart_le volume _)
  have hmono := measureReal_mono (μ:=G.measure.singularPart volume)
    (show {a} ⊆ Icc a b from singleton_subset_iff.mpr ⟨le_rfl,hab⟩) hsing
  rw [hatom] at hmono
  have hvar : 0 ≤ ∫ r in Icc a b,transportVariationDensity (deriv G r) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
    rw [hr]
    exact (transportVariationDensity_bounds ENNReal.toReal_nonneg).1
  unfold matchingVariation
  linarith

 theorem matching_initial_primitive_deficit {a b : ℝ} {M : ℝ≥0}
    {J Xi : ℝ → ℝ} (G : StieltjesFunction ℝ) (hab : a ≤ b)
    (hleft : leftLim G a=a) (hJ : LipschitzOnWith M J (Icc a b))
    (hmatch : ∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r)=Xi r) :
    Xi a-J a ≤ (M:ℝ)*matchingVariation G a b := by
  have ha : a ∈ Icc a b := ⟨le_rfl,hab⟩
  have h := hJ.dist_le_mul (G a) (hmatch a ha).1 a ha
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmatch a ha).1.1),
    (hmatch a ha).2] at h
  exact ((le_abs_self _).trans h).trans
    (mul_le_mul_of_nonneg_left (matching_initial_atom_le_variation G hab hleft) M.coe_nonneg)

 theorem matching_terminal_primitive_deficit {a b : ℝ} {M : ℝ≥0}
    {J Xi G : ℝ → ℝ} (hab : a ≤ b) (hJ : LipschitzOnWith M J (Icc a b))
    (hmatch : ∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r)=Xi r) :
    J b-Xi b ≤ (M:ℝ)*(b-G b) := by
  have hb : b ∈ Icc a b := ⟨hab,le_rfl⟩
  have h := hJ.dist_le_mul b hb (G b) (hmatch b hb).1
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmatch b hb).1.2),
    (hmatch b hb).2] at h
  exact (le_abs_self _).trans h

 theorem Admissible.tail_slack_integral {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r ∈ Icc ell tEnd) :
    (∫ t in r..tEnd,lam-t-d.phi t)=d.S-quadratic lam r+lowPrimitive lam d r := by
  have hline : IntervalIntegrable (fun t : ℝ => lam-t) volume r tEnd :=
    (by fun_prop : Continuous (fun t : ℝ => lam-t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hline
    (hd.intervalIntegrable hr.1 hr.2 le_rfl),integral_line,
    ← hd.lowPrimitive_sub hr (show tEnd ∈ Icc ell tEnd by norm_num [ell,tEnd]),hd.2.2.2.2.1]
  ring

end OptimalG.Variational
