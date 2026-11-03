import OptimalG.VariationalInactiveBump
import Mathlib.Analysis.SpecificLimits.Basic

/-! Measurable inactive sets must saturate the line score bound. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

noncomputable def scoreSlackBump (lam eta : ℝ) (d : LowRankData) (E : Set ℝ) : ℝ → ℝ :=
  E.indicator (fun r => min 1 (max 0 (lam-r-d.phi r-eta)))

theorem scoreSlackBump_bounds (lam eta : ℝ) (d : LowRankData) (E : Set ℝ) (r : ℝ) :
    0 ≤ scoreSlackBump lam eta d E r ∧ scoreSlackBump lam eta d E r ≤ 1 := by
  unfold scoreSlackBump
  by_cases hr : r ∈ E
  · rw [indicator_of_mem hr]
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  · simp only [indicator_of_notMem hr]
    norm_num

theorem scoreSlackBump_ne_zero_mem {lam eta r : ℝ} {d : LowRankData} {E : Set ℝ}
    (hh : scoreSlackBump lam eta d E r ≠ 0) : r ∈ E := by
  by_contra hr
  exact hh (indicator_of_notMem hr _)

theorem scoreSlackBump_score {lam eta r : ℝ} {d : LowRankData} {E : Set ℝ}
    (hh : scoreSlackBump lam eta d E r ≠ 0) : d.phi r ≤ lam-r-eta := by
  by_contra hnot
  have hval : lam-r-d.phi r-eta ≤ 0 := by linarith
  have he : scoreSlackBump lam eta d E r = 0 := by
    simp [scoreSlackBump,max_eq_left hval]
  exact hh he

theorem Admissible.scoreSlackBump_memLp_null {lam eta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {E : Set ℝ} (hE : NullMeasurableSet E (volume.restrict (Icc ell tEnd))) :
    MemLp (scoreSlackBump lam eta d E) ⊤ (volume.restrict (Icc ell tEnd)) := by
  have hm : AEStronglyMeasurable (fun r => lam-r-d.phi r-eta) (volume.restrict (Icc ell tEnd)) :=
    ((aestronglyMeasurable_const.sub measurable_id.aestronglyMeasurable).sub hd.2.2.1.aestronglyMeasurable).sub
      aestronglyMeasurable_const
  have hm' : AEStronglyMeasurable (scoreSlackBump lam eta d E) (volume.restrict (Icc ell tEnd)) :=
    (aestronglyMeasurable_const.inf (aestronglyMeasurable_const.sup hm)).indicator₀ hE
  apply memLp_top_of_bound hm' 1
  exact Eventually.of_forall fun r => by
    rw [Real.norm_eq_abs,abs_of_nonneg (scoreSlackBump_bounds lam eta d E r).1]
    exact (scoreSlackBump_bounds lam eta d E r).2

theorem Admissible.scoreSlackBump_memLp {lam eta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {E : Set ℝ} (hE : MeasurableSet E) :
    MemLp (scoreSlackBump lam eta d E) ⊤ (volume.restrict (Icc ell tEnd)) :=
  hd.scoreSlackBump_memLp_null hE.nullMeasurableSet

/-- Uniformly inactive measurable sets above a region of strict cap slack have
no residual score slack, almost everywhere. -/
theorem inactive_nullMeasurable_set_saturates {lam a m δ : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    {E : Set ℝ} (hE : NullMeasurableSet E (volume.restrict (Icc ell tEnd))) (hEa : E ⊆ Ioi a)
    (hm : 0 < m) (hcap : ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r)
    (hδ : 0 < δ)
    (hinactive : ∀ z ∈ Icc zStart zEnd, ∀ᵐ c ∂controlMeasure,
      (c.2.1 ∈ E ∨ c.2.2 ∈ E) →
        vectorField lam d z (continuation lam d z)+δ ≤ controlH lam d z (continuation lam d z) c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), r ∈ E → d.phi r = lam-r := by
  have hbound (eta : ℝ) (heta : 0 < eta) :
      ∀ᵐ r ∂volume.restrict (Icc ell tEnd), r ∈ E → lam-r-eta ≤ d.phi r := by
    let h := scoreSlackBump lam eta d E
    have hh := hd.scoreSlackBump_memLp_null (eta := eta) hE
    have hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r ∧ h r ≤ 1 :=
      Eventually.of_forall fun r => scoreSlackBump_bounds lam eta d E r
    have hzero : ∀ r ≤ a, h r = 0 := by
      intro r hr
      have hrn : r ∉ E := fun hrE => (not_lt_of_ge hr) (hEa hrE)
      exact indicator_of_notMem hrn _
    have hmass : bumpMass h = 0 := by
      have hnonneg : 0 ≤ bumpMass h := (bump_partial_bounds hh (hb.mono fun _ h => h.1)
        (r := tEnd) (by norm_num [ell,tEnd])).1
      apply le_antisymm _ hnonneg
      apply le_of_not_gt
      intro hpos
      apply no_inactive_positive_bump hd hl hmin hpass hh hb hpos hzero heta
        (Eventually.of_forall fun _ => scoreSlackBump_score) hm hcap hδ
      intro z hz
      filter_upwards [hinactive z hz] with c hc
      intro hnonzero
      exact hc (hnonzero.imp scoreSlackBump_ne_zero_mem scoreSlackBump_ne_zero_mem)
    have hi : (∫ r, h r ∂volume.restrict (Icc ell tEnd)) = 0 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num [ell,tEnd] : ell ≤ tEnd)]
      exact hmass
    have hae : h =ᵐ[volume.restrict (Icc ell tEnd)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (hb.mono fun _ h => h.1) (MemLp.integrable (by simp) hh)).mp hi
    filter_upwards [hae] with r hr
    intro hrE
    by_contra hnot
    have hval : 0 < lam-r-d.phi r-eta := by linarith
    have hpositive : 0 < h r := by
      dsimp [h,scoreSlackBump]
      rw [indicator_of_mem hrE]
      exact lt_min (by norm_num) (lt_max_of_lt_right hval)
    change h r = 0 at hr
    linarith
  have hall : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), ∀ n : ℕ,
      r ∈ E → lam-r-1/((n:ℝ)+1) ≤ d.phi r :=
    ae_all_iff.mpr fun n => hbound (1/((n:ℝ)+1)) (by positivity)
  filter_upwards [hall,hd.2.2.2.1] with r hr hceil
  intro hrE
  apply le_antisymm hceil.2
  have ht : Tendsto (fun n : ℕ => lam-r-1/((n:ℝ)+1)) atTop (𝓝 (lam-r)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := lam-r)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact le_of_tendsto' ht (fun n => hr n hrE)

theorem inactive_set_saturates {lam a m δ : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    {E : Set ℝ} (hE : MeasurableSet E) (hEa : E ⊆ Ioi a)
    (hm : 0 < m) (hcap : ∀ r ∈ Icc a tEnd, lowPrimitive lam d r+m ≤ cap lam d.S r)
    (hδ : 0 < δ)
    (hinactive : ∀ z ∈ Icc zStart zEnd, ∀ᵐ c ∂controlMeasure,
      (c.2.1 ∈ E ∨ c.2.2 ∈ E) →
        vectorField lam d z (continuation lam d z)+δ ≤ controlH lam d z (continuation lam d z) c) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), r ∈ E → d.phi r = lam-r :=
  inactive_nullMeasurable_set_saturates hd hl hmin hpass hE.nullMeasurableSet hEa hm hcap hδ hinactive

end OptimalG.Variational
