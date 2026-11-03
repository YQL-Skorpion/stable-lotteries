import OptimalG.VariationalWeightedODE
import OptimalG.VariationalAverageLimit
import OptimalG.VariationalODELimit

/-!
# Continuity of controls with frozen tent weights

The weights are fixed using the limiting admissible data. Weak convergence of
scores then gives convergence of each weighted control, and uniform elementary
bounds upgrade this to the integrated residual needed for ODE stability.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped Topology

/-- A fixed integrable nonnegative density may be absorbed into the control
measure, giving continuity of the genuine weighted rational control. -/
theorem weighted_controlH_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (w : Control → ℝ) (hw : Integrable w controlMeasure)
    (hw0 : ∀ᵐ c ∂controlMeasure, 0 ≤ w c) (z u : ℝ) :
    Tendsto (fun n => ∫ c, w c * controlH (lamn n) (dn n) z u c ∂controlMeasure) atTop
      (𝓝 (∫ c, w c * controlH lam d z u c ∂controlMeasure)) := by
  let ν : Measure Control := controlMeasure.withDensity (fun c => ENNReal.ofReal (w c))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hw.2
  have hν : ν ≪ controlMeasure := withDensity_absolutelyContinuous _ _
  have heq (F : Control → ℝ) : (∫ c, F c ∂ν) = ∫ c, w c * F c ∂controlMeasure := by
    calc
      _ = ∫ c, (ENNReal.ofReal (w c)).toReal * F c ∂controlMeasure :=
        integral_withDensity_eq_integral_toReal_smul₀ hw.1.aemeasurable.ennreal_ofReal
          (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hw0] with c hc
        rw [ENNReal.toReal_ofReal hc]
  simpa only [heq] using average_controlH_tendsto_of_data lamn dn hn hd hlam hS hJ ν hν z u

theorem frozenTentField_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam lamRef : ℝ} {d dRef : LowRankData} (hd : Admissible lam d)
    (href : Admissible lamRef dRef)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (Yref : ℝ → ℝ) {eps : ℝ} (heps : 0 ≤ eps) (z u : ℝ) :
    Tendsto (fun n => frozenTentField (lamn n) (dn n) lamRef dRef Yref eps z u) atTop
      (𝓝 (frozenTentField lam d lamRef dRef Yref eps z u)) := by
  have hw := href.pathControlWeight_bounds Yref heps z
  have hwb : EssentiallyBounded (pathControlWeight lamRef dRef Yref eps z) controlMeasure := by
    refine ⟨eps, ?_⟩
    filter_upwards [hw] with c hc
    rw [abs_of_nonneg hc.1]
    exact hc.2
  have hwi := hwb.integrable
    (aestronglyMeasurable_tentWeight (href.controlH_measurable z (Yref z)) _ _)
  have hi := weighted_controlH_tendsto_of_data lamn dn hn hd hlam hS hJ
    (pathControlWeight lamRef dRef Yref eps z) hwi (hw.mono fun _ h => h.1) z u
  exact ((tendsto_const_nhds.mul (hlam.sub_const z)).add hi).div_const _

/-- On every fixed continuous state path the residual of the frozen fields
converges to zero in L¹ over the entire continuation interval. -/
theorem frozenTentField_integrated_residual_tendsto
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam lamRef : ℝ} {d dRef : LowRankData} (hd : Admissible lam d)
    (href : Admissible lamRef dRef)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (Yref Z : ℝ → ℝ) (hY : ContinuousOn Yref (Icc zStart zEnd))
    (hZ : ContinuousOn Z (Icc zStart zEnd)) {eps : ℝ} (heps : 0 < eps) :
    Tendsto (fun n => ∫ z in zStart..zEnd,
      |frozenTentField (lamn n) (dn n) lamRef dRef Yref eps z (Z z) -
        frozenTentField lam d lamRef dRef Yref eps z (Z z)|) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ
  let B := 100 * (19 + 3 * max C 0)
  have hZB : ∀ z ∈ Icc zStart zEnd, |Z z| ≤ max C 0 := by
    intro z hz
    exact (hC z hz).trans (le_max_left _ _)
  have hbound (n : ℕ) (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      |frozenTentField (lamn n) (dn n) lamRef dRef Yref eps z (Z z) -
        frozenTentField lam d lamRef dRef Yref eps z (Z z)| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by
      have hbn := (hn n).frozenTentField_uniform_bound href Yref Z heps
        (max C 0) (le_max_right _ _) hZB z hz
      have hb := hd.frozenTentField_uniform_bound href Yref Z heps
        (max C 0) (le_max_right _ _) hZB z hz
      dsimp [B]
      linarith)
  have hle : zStart ≤ zEnd := by norm_num [zStart, zEnd]
  have ht : Tendsto (fun n => ∫ z in zStart..zEnd,
      |frozenTentField (lamn n) (dn n) lamRef dRef Yref eps z (Z z) -
        frozenTentField lam d lamRef dRef Yref eps z (Z z)|) atTop
      (𝓝 (∫ _z in zStart..zEnd, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
    · apply Eventually.of_forall
      intro n
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      exact (((hn n).frozenTentField_continuous_path href Yref Z hY hZ heps).sub
        (hd.frozenTentField_continuous_path href Yref Z hY hZ heps)).abs.mono
        (uIoc_subset_uIcc.trans (by rw [uIcc_of_le hle]))
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro z hz
      simpa only [Real.norm_eq_abs, abs_abs] using hbound n z
        (by simpa only [uIcc_of_le hle] using uIoc_subset_uIcc hz)
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro z _
      simpa only [sub_self, abs_zero] using
        ((frozenTentField_tendsto_of_data lamn dn hn hd href hlam hS hJ Yref heps.le z (Z z)).sub
          (tendsto_const_nhds (x := frozenTentField lam d lamRef dRef Yref eps z (Z z)))).abs
  simpa using ht

/-- Trajectories of frozen controls converge uniformly under the weak-* data
convergence furnished by compactness of the low-rank primitives. -/
theorem frozenTentTrajectory_tendstoUniformlyOn
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam lamRef : ℝ} {d dRef : LowRankData} (hd : Admissible lam d)
    (href : Admissible lamRef dRef)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (Yref : ℝ → ℝ) (hY : ContinuousOn Yref (Icc zStart zEnd)) {eps : ℝ} (heps : 0 < eps)
    (Zn : ℕ → ℝ → ℝ) (Z : ℝ → ℝ)
    (hZn : ∀ n, IsFieldTrajectory (frozenTentField (lamn n) (dn n) lamRef dRef Yref eps)
      (quadratic (lamn n) zStart - (dn n).S) (Zn n))
    (hZ : IsFieldTrajectory (frozenTentField lam d lamRef dRef Yref eps)
      (quadratic lam zStart - d.S) Z) :
    TendstoUniformlyOn Zn Z atTop (Icc zStart zEnd) := by
  apply scalar_ode_solutions_tendstoUniformlyOn
    (fun n => frozenTentField (lamn n) (dn n) lamRef dRef Yref eps)
    (frozenTentField lam d lamRef dRef Yref eps) (19 / 2) Zn Z zStart zEnd
    (by norm_num [zStart, zEnd])
    (fun n z _ => (hn n).frozenTentField_lipschitz href Yref heps z)
    hZ.continuous (fun n => (hZn n).continuous)
    (fun z hz => hZ.right_derivative hz) (fun n z hz => (hZn n).right_derivative hz)
    (fun n => (((hn n).frozenTentField_continuous_path href Yref Z hY hZ.continuous heps).sub
      (hd.frozenTentField_continuous_path href Yref Z hY hZ.continuous heps)).abs)
  · simp only [(hZn _).1, hZ.1, quadratic]
    exact ((hlam.mul_const zStart).sub_const (zStart ^ 2 / 2)).sub hS
  · exact frozenTentField_integrated_residual_tendsto lamn dn hn hd href hlam hS hJ
      Yref Z hY hZ.continuous heps

end OptimalG.Variational
