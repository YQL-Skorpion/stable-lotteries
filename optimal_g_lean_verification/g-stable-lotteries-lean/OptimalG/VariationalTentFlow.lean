import OptimalG.VariationalTent
import OptimalG.VariationalControlLimit

/-!
# Tent averages along a continuation

The density is selected from a fixed reference trajectory. Once selected it
remains fixed when the low-rank data vary, as required for the lower
semicontinuity argument in Appendix B.2.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter Metric
open scoped NNReal Topology

theorem Admissible.vectorField_continuous {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : Continuous (fun v : ℝ × ℝ => vectorField lam d v.1 v.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ (19 / 2)
    h.vectorField_lipschitz h.vectorField_continuous_time

theorem Admissible.controlH_uniform_bound {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hY : ∀ z ∈ Icc zStart zEnd, |Y z| ≤ C) :
    ∀ z ∈ Icc zStart zEnd, ∀ᵐ c ∂controlMeasure,
      |controlH lam d z (Y z) c| ≤ 100 * (19 + 3 * C) := by
  intro z hz
  have hza : |z| ≤ 1 := by
    have hz0 := hz.1
    have hz1 := hz.2
    norm_num [zStart, zEnd] at hz0 hz1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hzb : (|z| + 1) ^ 2 ≤ 4 := by nlinarith [abs_nonneg z]
  have hCb : controlCoeffBound z (Y z) ≤ 100 * (19 + 3 * C) := by
    unfold controlCoeffBound
    linarith [hY z hz]
  have hB : 0 ≤ 100 * (19 + 3 * C) := by positivity
  have hmem : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  filter_upwards [hmem, h.control_phi_bounds] with c hc hphi
  have hb := h.control_coefficients_bound z (Y z) hc
  have hfx : |d.phi c.2.1| ≤ (278 : ℝ) / 1000 := by
    rw [abs_of_nonneg hphi.1.1]
    exact hphi.1.2
  have hfy : |d.phi c.2.2| ≤ (278 : ℝ) / 1000 := by
    rw [abs_of_nonneg hphi.2.1]
    exact hphi.2.2
  rw [controlH_linear_scores]
  calc
    _ ≤ |controlCoeffX lam d z (Y z) c| * |d.phi c.2.1| +
        |controlCoeffY lam d z (Y z) c| * |d.phi c.2.2| := by
      simpa only [abs_mul] using abs_add_le
        (controlCoeffX lam d z (Y z) c * d.phi c.2.1)
        (controlCoeffY lam d z (Y z) c * d.phi c.2.2)
    _ ≤ (100 * (19 + 3 * C)) * ((278 : ℝ) / 1000) +
        (100 * (19 + 3 * C)) * ((278 : ℝ) / 1000) := add_le_add
      (mul_le_mul (hb.1.trans hCb) hfx (abs_nonneg _) hB)
      (mul_le_mul (hb.2.trans hCb) hfy (abs_nonneg _) hB)
    _ ≤ _ := by nlinarith

noncomputable def pathControlWeight (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ)
    (eps z : ℝ) (c : Control) : ℝ :=
  tentWeight (vectorField lam d z (Y z)) eps (controlH lam d z (Y z) c)

noncomputable def pathLineWeight (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ)
    (eps z : ℝ) : ℝ :=
  tentWeight (vectorField lam d z (Y z)) eps (lam - z)

noncomputable def weightedField (lam : ℝ) (d : LowRankData)
    (w0 : ℝ → ℝ) (w : ℝ → Control → ℝ) (z u : ℝ) : ℝ :=
  (w0 z * (lam - z) + ∫ c, w z c * controlH lam d z u c ∂controlMeasure) /
    (w0 z + ∫ c, w z c ∂controlMeasure)

noncomputable def tentField (lam : ℝ) (d : LowRankData) (Y : ℝ → ℝ) (eps : ℝ) : ℝ → ℝ → ℝ :=
  weightedField lam d (pathLineWeight lam d Y eps) (pathControlWeight lam d Y eps)

theorem Admissible.pathControlWeight_bounds {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) {eps : ℝ} (heps : 0 ≤ eps) (z : ℝ) :
    ∀ᵐ c ∂controlMeasure, 0 ≤ pathControlWeight lam d Y eps z c ∧
      pathControlWeight lam d Y eps z c ≤ eps := by
  filter_upwards [ae_essInf_le (h.controlH_bounded z (Y z)).boundedBelow] with c hc
  exact ⟨tentWeight_nonneg _ _ _, tentWeight_le_eps _ _ _ heps ((min_le_right _ _).trans hc)⟩

theorem Admissible.tentField_gap {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (z : ℝ) :
    vectorField lam d z (Y z) ≤ tentField lam d Y eps z (Y z) ∧
      tentField lam d Y eps z (Y z) ≤ vectorField lam d z (Y z) + eps :=
  tentAverage_bounds (controlH lam d z (Y z)) (lam - z) eps heps
    (h.controlH_bounded z (Y z)) (h.controlH_measurable z (Y z))

theorem Admissible.tent_denominator_positive {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (z : ℝ) :
    0 < pathLineWeight lam d Y eps z + ∫ c, pathControlWeight lam d Y eps z c ∂controlMeasure :=
  tent_denominator_pos (controlH lam d z (Y z)) (lam - z) eps heps
    (h.controlH_bounded z (Y z)) (h.controlH_measurable z (Y z))

theorem Admissible.controlH_continuous_time_path {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd))
    (c : Control) : ContinuousOn (fun z => controlH lam d z (Y z) c) (Icc zStart zEnd) := by
  unfold controlH quadratic
  fun_prop

theorem Admissible.path_moment_continuous
    {lam lam' : ℝ} {d d' : LowRankData} (h : Admissible lam d) (h' : Admissible lam' d')
    (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd)) {eps : ℝ} (heps : 0 ≤ eps) (u : ℝ) :
    ContinuousOn (fun z => ∫ c, pathControlWeight lam d Y eps z c * controlH lam' d' z u c
      ∂controlMeasure) (Icc zStart zEnd) := by
  apply continuousOn_tent_moment (Icc zStart zEnd)
    (fun z c => controlH lam d z (Y z) c) (fun z c => controlH lam' d' z u c)
    (fun z => vectorField lam d z (Y z)) eps (100 * (19 + 3 * |u|)) heps
  · exact h.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hY)
  · intro z _
    exact h.controlH_measurable z (Y z)
  · intro z _
    exact h'.controlH_measurable z u
  · exact Eventually.of_forall (fun c => h.controlH_continuous_time_path Y hY c)
  · exact Eventually.of_forall (fun c => h'.controlH_continuous_time_path (fun _ => u) continuousOn_const c)
  · intro z _
    filter_upwards [ae_essInf_le (h.controlH_bounded z (Y z)).boundedBelow] with c hc
    exact (min_le_right _ _).trans hc
  · exact h'.controlH_uniform_bound (fun _ => u) |u| (abs_nonneg _) (fun _ _ => le_rfl)

theorem Admissible.path_denominator_continuous {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd))
    {eps : ℝ} (heps : 0 ≤ eps) :
    ContinuousOn (fun z => pathLineWeight lam d Y eps z +
      ∫ c, pathControlWeight lam d Y eps z c ∂controlMeasure) (Icc zStart zEnd) := by
  have hm := h.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hY)
  have hw0 : ContinuousOn (pathLineWeight lam d Y eps) (Icc zStart zEnd) := by
    unfold pathLineWeight tentWeight
    exact continuousOn_const.sup ((hm.add_const eps).sub (continuousOn_const.sub continuousOn_id))
  have hi := continuousOn_tent_moment (Icc zStart zEnd)
    (fun z c => controlH lam d z (Y z) c) (fun _ _ => (1 : ℝ))
    (fun z => vectorField lam d z (Y z)) eps 1 heps hm
    (fun z _ => h.controlH_measurable z (Y z)) (fun _ _ => aestronglyMeasurable_const)
    (Eventually.of_forall (fun c => h.controlH_continuous_time_path Y hY c))
    (Eventually.of_forall (fun _ => continuousOn_const))
    (fun z _ => (ae_essInf_le (h.controlH_bounded z (Y z)).boundedBelow).mono
      (fun _ hc => (min_le_right _ _).trans hc))
    (fun _ _ => Eventually.of_forall (fun _ => by norm_num))
  have hi' : ContinuousOn (fun z => ∫ c, pathControlWeight lam d Y eps z c ∂controlMeasure)
      (Icc zStart zEnd) := by
    change ContinuousOn (fun z => ∫ c, tentWeight (vectorField lam d z (Y z)) eps
      (controlH lam d z (Y z) c) ∂controlMeasure) (Icc zStart zEnd)
    simpa only [mul_one] using hi
  exact hw0.add hi'

/-- Nonnegative weighted averages inherit the common state Lipschitz constant.
The line branch contributes zero to the state derivative. -/
theorem Admissible.weightedField_lipschitz {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (w0 : ℝ → ℝ) (w : ℝ → Control → ℝ) (z E : ℝ)
    (hm : AEStronglyMeasurable (w z) controlMeasure)
    (hw : ∀ᵐ c ∂controlMeasure, 0 ≤ w z c ∧ w z c ≤ E)
    (hw0 : 0 ≤ w0 z) (hD : 0 < w0 z + ∫ c, w z c ∂controlMeasure) :
    LipschitzWith (19 / 2 : ℝ≥0) (weightedField lam d w0 w z) := by
  have hwb : EssentiallyBounded (w z) controlMeasure := by
    refine ⟨E, ?_⟩
    filter_upwards [hw] with c hc
    rw [abs_of_nonneg hc.1]
    exact hc.2
  have hwi := hwb.integrable hm
  have hint (u : ℝ) : Integrable (fun c => w z c * controlH lam d z u c) controlMeasure :=
    (hwb.mul (h.controlH_bounded z u)).integrable (hm.mul (h.controlH_measurable z u))
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have heq : weightedField lam d w0 w z u - weightedField lam d w0 w z v =
      (∫ c, w z c * (controlH lam d z u c - controlH lam d z v c) ∂controlMeasure) /
        (w0 z + ∫ c, w z c ∂controlMeasure) := by
    unfold weightedField
    rw [← sub_div, add_sub_add_left_eq_sub, ← integral_sub (hint u) (hint v)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun _ => by ring)
  rw [Real.dist_eq, heq, abs_div, abs_of_pos hD, Real.dist_eq]
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
  apply (div_le_iff₀ hD).mpr
  have hb : ∀ᵐ c ∂controlMeasure,
      ‖w z c * (controlH lam d z u c - controlH lam d z v c)‖ ≤
        w z c * ((19 : ℝ) / 2 * |u - v|) := by
    filter_upwards [hw, h.controlAlpha_bound] with c hwc hAc
    have heqH : controlH lam d z u c - controlH lam d z v c = controlAlpha lam d c * (u - v) := by
      rw [controlH_affine lam d z u c, controlH_affine lam d z v c]
      ring
    rw [heqH]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwc.1]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hAc (abs_nonneg _)) hwc.1
  have hi := norm_integral_le_of_norm_le
    (hwi.mul_const ((19 : ℝ) / 2 * |u - v|)) hb
  rw [Real.norm_eq_abs, integral_mul_const] at hi
  have hnonneg : 0 ≤ (19 : ℝ) / 2 * |u - v| := by positivity
  nlinarith [mul_nonneg hw0 hnonneg]

/-- A field using weights selected once from the reference data, and rational
controls evaluated at potentially different target data. -/
noncomputable def frozenTentField (lam : ℝ) (d : LowRankData)
    (lamRef : ℝ) (dRef : LowRankData) (Y : ℝ → ℝ) (eps : ℝ) : ℝ → ℝ → ℝ :=
  weightedField lam d (pathLineWeight lamRef dRef Y eps) (pathControlWeight lamRef dRef Y eps)

theorem Admissible.frozenTentField_lipschitz
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Y : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (z : ℝ) :
    LipschitzWith (19 / 2 : ℝ≥0) (frozenTentField lam d lamRef dRef Y eps z) :=
  h.weightedField_lipschitz _ _ z eps
    (aestronglyMeasurable_tentWeight (href.controlH_measurable z (Y z)) _ _)
    (href.pathControlWeight_bounds Y heps.le z) (tentWeight_nonneg _ _ _)
    (href.tent_denominator_positive Y heps z)

theorem Admissible.frozenTentField_continuous_time
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd)) {eps : ℝ} (heps : 0 < eps) (u : ℝ) :
    ContinuousOn (fun z => frozenTentField lam d lamRef dRef Y eps z u) (Icc zStart zEnd) := by
  have hm := href.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hY)
  have hw0 : ContinuousOn (pathLineWeight lamRef dRef Y eps) (Icc zStart zEnd) := by
    unfold pathLineWeight tentWeight
    exact continuousOn_const.sup ((hm.add_const eps).sub (continuousOn_const.sub continuousOn_id))
  exact ((hw0.mul (continuousOn_const.sub continuousOn_id)).add
    (href.path_moment_continuous h Y hY heps.le u)).div
    (href.path_denominator_continuous Y hY heps.le)
    (fun z _ => (href.tent_denominator_positive Y heps z).ne')

/-- Every nonnegative weighted control average dominates the envelope field. -/
theorem Admissible.vectorField_le_weightedField {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (w0 : ℝ → ℝ) (w : ℝ → Control → ℝ) (z u E : ℝ)
    (hm : AEStronglyMeasurable (w z) controlMeasure)
    (hw : ∀ᵐ c ∂controlMeasure, 0 ≤ w z c ∧ w z c ≤ E)
    (hw0 : 0 ≤ w0 z) (hD : 0 < w0 z + ∫ c, w z c ∂controlMeasure) :
    vectorField lam d z u ≤ weightedField lam d w0 w z u := by
  have hwb : EssentiallyBounded (w z) controlMeasure := by
    refine ⟨E, ?_⟩
    filter_upwards [hw] with c hc
    rw [abs_of_nonneg hc.1]
    exact hc.2
  have hwi := hwb.integrable hm
  have hi := (hwb.mul (h.controlH_bounded z u)).integrable (hm.mul (h.controlH_measurable z u))
  have hlow : ∀ᵐ c ∂controlMeasure, w z c * vectorField lam d z u ≤ w z c * controlH lam d z u c := by
    filter_upwards [hw, ae_essInf_le (h.controlH_bounded z u).boundedBelow] with c hwc hc
    exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hc) hwc.1
  have hl := integral_mono_ae (hwi.mul_const (vectorField lam d z u)) hi hlow
  rw [integral_mul_const] at hl
  have hline := mul_le_mul_of_nonneg_left (vectorField_le_line lam d z u) hw0
  apply (le_div_iff₀ hD).mpr
  nlinarith

theorem Admissible.vectorField_le_frozenTentField
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Y : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (z u : ℝ) :
    vectorField lam d z u ≤ frozenTentField lam d lamRef dRef Y eps z u :=
  h.vectorField_le_weightedField _ _ z u eps
    (aestronglyMeasurable_tentWeight (href.controlH_measurable z (Y z)) _ _)
    (href.pathControlWeight_bounds Y heps.le z) (tentWeight_nonneg _ _ _)
    (href.tent_denominator_positive Y heps z)

/-- A normalized nonnegative average cannot exceed a common absolute bound on
its constituent controls. -/
theorem Admissible.weightedField_abs_le {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (w0 : ℝ → ℝ) (w : ℝ → Control → ℝ) (z u E B : ℝ)
    (hm : AEStronglyMeasurable (w z) controlMeasure)
    (hw : ∀ᵐ c ∂controlMeasure, 0 ≤ w z c ∧ w z c ≤ E)
    (hw0 : 0 ≤ w0 z) (hD : 0 < w0 z + ∫ c, w z c ∂controlMeasure)
    (hline : |lam - z| ≤ B) (hctrl : ∀ᵐ c ∂controlMeasure, |controlH lam d z u c| ≤ B) :
    |weightedField lam d w0 w z u| ≤ B := by
  have hwb : EssentiallyBounded (w z) controlMeasure := by
    refine ⟨E, ?_⟩
    filter_upwards [hw] with c hc
    rw [abs_of_nonneg hc.1]
    exact hc.2
  have hwi := hwb.integrable hm
  have hi : ‖∫ c, w z c * controlH lam d z u c ∂controlMeasure‖ ≤
      (∫ c, w z c ∂controlMeasure) * B := by
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (hwi.mul_const B)
    filter_upwards [hw, hctrl] with c hwc hcc
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwc.1]
    exact mul_le_mul_of_nonneg_left hcc hwc.1
  unfold weightedField
  rw [abs_div, abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  have htri := abs_add_le (w0 z * (lam - z))
    (∫ c, w z c * controlH lam d z u c ∂controlMeasure)
  rw [abs_mul, abs_of_nonneg hw0] at htri
  rw [Real.norm_eq_abs] at hi
  have hl := mul_le_mul_of_nonneg_left hline hw0
  nlinarith

theorem Admissible.frozenTentField_uniform_bound
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Yref Z : ℝ → ℝ) {eps : ℝ} (heps : 0 < eps) (C : ℝ) (hC : 0 ≤ C)
    (hZ : ∀ z ∈ Icc zStart zEnd, |Z z| ≤ C) :
    ∀ z ∈ Icc zStart zEnd, |frozenTentField lam d lamRef dRef Yref eps z (Z z)| ≤ 100 * (19 + 3 * C) := by
  intro z hz
  change |weightedField lam d (pathLineWeight lamRef dRef Yref eps)
    (pathControlWeight lamRef dRef Yref eps) z (Z z)| ≤ 100 * (19 + 3 * C)
  apply h.weightedField_abs_le (pathLineWeight lamRef dRef Yref eps)
    (pathControlWeight lamRef dRef Yref eps) z (Z z) eps (100 * (19 + 3 * C))
    (aestronglyMeasurable_tentWeight (href.controlH_measurable z (Yref z)) _ _)
    (href.pathControlWeight_bounds Yref heps.le z) (tentWeight_nonneg _ _ _)
    (href.tent_denominator_positive Yref heps z)
  · have hlo := h.1.1
    have hhi := h.1.2
    have hzlo := hz.1
    have hzhi := hz.2
    norm_num [lambdaLo, lambdaHi, zStart, zEnd] at hlo hhi hzlo hzhi
    apply abs_le.mpr
    constructor <;> linarith
  · exact h.controlH_uniform_bound Z C hC hZ z hz

theorem Admissible.frozenTentField_continuous_path
    {lam lamRef : ℝ} {d dRef : LowRankData} (h : Admissible lam d) (href : Admissible lamRef dRef)
    (Yref Z : ℝ → ℝ) (hY : ContinuousOn Yref (Icc zStart zEnd))
    (hZ : ContinuousOn Z (Icc zStart zEnd)) {eps : ℝ} (heps : 0 < eps) :
    ContinuousOn (fun z => frozenTentField lam d lamRef dRef Yref eps z (Z z)) (Icc zStart zEnd) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ
  have hZB : ∀ z ∈ Icc zStart zEnd, |Z z| ≤ max C 0 := by
    intro z hz
    exact (hC z hz).trans (le_max_left _ _)
  have hm := href.vectorField_continuous.comp_continuousOn (continuousOn_id.prodMk hY)
  have hi := continuousOn_tent_moment (Icc zStart zEnd)
    (fun z c => controlH lamRef dRef z (Yref z) c) (fun z c => controlH lam d z (Z z) c)
    (fun z => vectorField lamRef dRef z (Yref z)) eps (100 * (19 + 3 * max C 0)) heps.le hm
    (fun z _ => href.controlH_measurable z (Yref z)) (fun z _ => h.controlH_measurable z (Z z))
    (Eventually.of_forall (fun c => href.controlH_continuous_time_path Yref hY c))
    (Eventually.of_forall (fun c => h.controlH_continuous_time_path Z hZ c))
    (fun z _ => (ae_essInf_le (href.controlH_bounded z (Yref z)).boundedBelow).mono
      (fun _ hc => (min_le_right _ _).trans hc))
    (h.controlH_uniform_bound Z (max C 0) (le_max_right _ _) hZB)
  have hw0 : ContinuousOn (pathLineWeight lamRef dRef Yref eps) (Icc zStart zEnd) := by
    unfold pathLineWeight tentWeight
    exact continuousOn_const.sup ((hm.add_const eps).sub (continuousOn_const.sub continuousOn_id))
  exact ((hw0.mul (continuousOn_const.sub continuousOn_id)).add hi).div
    (href.path_denominator_continuous Yref hY heps.le)
    (fun z _ => (href.tent_denominator_positive Yref heps z).ne')

end OptimalG.Variational
