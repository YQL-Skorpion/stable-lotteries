import OptimalG.VariationalStrongControl

/-! Norm continuity of the genuine maximal continuation. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem Admissible.vectorField_uniform_bound {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Z : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ z ∈ Icc zStart zEnd, |Z z| ≤ C) :
    ∀ z ∈ Icc zStart zEnd, |vectorField lam d z (Z z)| ≤ 100 * (19 + 3*C) := by
  intro z hz
  let B := 100 * (19 + 3*C)
  have hc := h.controlH_uniform_bound Z C hC hZ z hz
  have hb := h.controlH_bounded z (Z z)
  have hlo : -B ≤ essInf (controlH lam d z (Z z)) controlMeasure :=
    le_essInf_of_ae_le (-B) (hc.mono fun _ hi => (abs_le.mp hi).1)
      hb.boundedAbove.isCoboundedUnder_ge
  have hl := h.1.1
  have hu := h.1.2
  have hzl := hz.1
  have hzu := hz.2
  norm_num [lambdaLo, lambdaHi, zStart, zEnd] at hl hu hzl hzu
  have hline : |lam-z| ≤ B := by
    dsimp [B]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact abs_le.mpr ⟨le_min (abs_le.mp hline).1 hlo,
    (vectorField_le_line lam d z (Z z)).trans (abs_le.mp hline).2⟩

theorem vectorField_integrated_residual_tendsto
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)))
    (Z : ℝ → ℝ) (hZ : ContinuousOn Z (Icc zStart zEnd)) :
    Tendsto (fun n => ∫ z in zStart..zEnd,
      |vectorField (lamn n) (dn n) z (Z z) - vectorField lam d z (Z z)|) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ
  let B := 100 * (19 + 3 * max C 0)
  have hZB : ∀ z ∈ Icc zStart zEnd, |Z z| ≤ max C 0 := by
    intro z hz
    exact (hC z hz).trans (le_max_left _ _)
  have hbound (n : ℕ) (z : ℝ) (hz : z ∈ Icc zStart zEnd) :
      |vectorField (lamn n) (dn n) z (Z z) - vectorField lam d z (Z z)| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by
      have hbn := (hn n).vectorField_uniform_bound Z (max C 0) (le_max_right _ _) hZB z hz
      have hb := hd.vectorField_uniform_bound Z (max C 0) (le_max_right _ _) hZB z hz
      dsimp [B]
      linarith)
  have hle : zStart ≤ zEnd := by norm_num [zStart, zEnd]
  have ht : Tendsto (fun n => ∫ z in zStart..zEnd,
      |vectorField (lamn n) (dn n) z (Z z) - vectorField lam d z (Z z)|) atTop
      (𝓝 (∫ _z in zStart..zEnd, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * B)
    · apply Eventually.of_forall
      intro n
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      exact (((hn n).vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hZ)).sub
        (hd.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hZ))).abs.mono
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
        ((vectorField_tendsto_of_strong_data lamn dn hn hd hlam hS hJ hphi z (Z z)).sub
          (tendsto_const_nhds (x := vectorField lam d z (Z z)))).abs
  simpa using ht

/-- Uniform continuity of the actual continuation along every strongly
convergent sequence of admissible data. -/
theorem continuation_tendstoUniformlyOn_of_strong_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd))) :
    TendstoUniformlyOn (fun n => continuation (lamn n) (dn n)) (continuation lam d)
      atTop (Icc zStart zEnd) := by
  apply scalar_ode_solutions_tendstoUniformlyOn
    (fun n => vectorField (lamn n) (dn n)) (vectorField lam d) (19 / 2)
    (fun n => continuation (lamn n) (dn n)) (continuation lam d) zStart zEnd
    (by norm_num [zStart, zEnd]) (fun n z _ => (hn n).vectorField_lipschitz z)
    (continuation_continuous hd.isContinuation) (fun n => continuation_continuous (hn n).isContinuation)
    (fun z hz => hd.isContinuation.right_derivative hz)
    (fun n z hz => (hn n).isContinuation.right_derivative hz)
    (fun n => (((hn n).vectorField_continuous.comp_continuousOn
      (continuousOn_id.prodMk (continuation_continuous hd.isContinuation))).sub
      (hd.vectorField_continuous.comp_continuousOn
        (continuousOn_id.prodMk (continuation_continuous hd.isContinuation)))).abs)
  · simp only [(hn _).isContinuation.1, hd.isContinuation.1, quadratic]
    exact ((hlam.mul_const zStart).sub_const (zStart ^ 2 / 2)).sub hS
  · exact vectorField_integrated_residual_tendsto lamn dn hn hd hlam hS hJ hphi
      (continuation lam d) (continuation_continuous hd.isContinuation)

end OptimalG.Variational
