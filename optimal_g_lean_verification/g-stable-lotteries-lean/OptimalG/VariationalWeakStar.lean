import OptimalG.VariationalRecovery
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Testing low-rank scores against integrable densities

A common essential bound makes the integral pairings equicontinuous on L¹.
Consequently convergence against smooth test functions extends to every L¹
marginal density used by the averaged controls in Appendix B.2.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction ContDiff

noncomputable def scorePairing {mu : Measure ℝ} (phi : ℝ → ℝ) (f : Lp ℝ 1 mu) : ℝ :=
  ∫ r, phi r * f r ∂mu

/-- The dual pairing with a bounded score is Lipschitz on L¹ with exactly its
essential bound as a Lipschitz constant. -/
theorem scorePairing_lipschitz {mu : Measure ℝ} (phi : ℝ → ℝ) (K : ℝ≥0)
    (hphi : AEStronglyMeasurable phi mu) (hbound : ∀ᵐ r ∂mu, ‖phi r‖ ≤ K) :
    LipschitzWith K (scorePairing phi : Lp ℝ 1 mu → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hf : Integrable (fun r => f r) mu := memLp_one_iff_integrable.mp (Lp.memLp f)
  have hg : Integrable (fun r => g r) mu := memLp_one_iff_integrable.mp (Lp.memLp g)
  have hpf := hf.bdd_mul hphi hbound
  have hpg := hg.bdd_mul hphi hbound
  rw [Real.dist_eq]
  unfold scorePairing
  rw [← integral_sub hpf hpg]
  have hnorm : ∀ᵐ r ∂mu, ‖phi r * f r - phi r * g r‖ ≤ K * ‖f r - g r‖ := by
    filter_upwards [hbound] with r hr
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
  have hi := norm_integral_le_of_norm_le ((hf.sub hg).norm.const_mul (K : ℝ)) hnorm
  rw [integral_const_mul] at hi
  rw [L1.dist_eq_integral_dist]
  simpa only [Real.norm_eq_abs, Real.dist_eq, Pi.sub_apply] using hi

/-- It suffices to prove convergence against smooth compactly supported tests.
The conclusion quantifies over every L¹ function, matching weak-star convergence. -/
theorem scorePairing_tendsto_of_smooth_tests
    {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu]
    (phin : ℕ → ℝ → ℝ) (phi : ℝ → ℝ) (K : ℝ≥0)
    (hnmeas : ∀ n, AEStronglyMeasurable (phin n) mu)
    (hnbound : ∀ n, ∀ᵐ r ∂mu, ‖phin n r‖ ≤ K)
    (hmeas : AEStronglyMeasurable phi mu)
    (hbound : ∀ᵐ r ∂mu, ‖phi r‖ ≤ K)
    (hsmooth : ∀ g : ℝ → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      Tendsto (fun n => ∫ r, phin n r * g r ∂mu) atTop (𝓝 (∫ r, phi r * g r ∂mu))) :
    ∀ f : Lp ℝ 1 mu, Tendsto (fun n => scorePairing (phin n) f) atTop (𝓝 (scorePairing phi f)) := by
  let D : Set (Lp ℝ 1 mu) :=
    {f | ∃ g : ℝ → ℝ, f =ᵐ[mu] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}
  have hdense : Dense D := Lp.dense_hasCompactSupport_contDiff (by simp)
  have hequi : Equicontinuous (fun n => (scorePairing (phin n) : Lp ℝ 1 mu → ℝ)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (K : ℝ) * r)
      (by simpa using (tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun r : ℝ => (K : ℝ) * r) (𝓝 0) (𝓝 ((K : ℝ) * 0))))
    intro f g n
    exact (scorePairing_lipschitz (phin n) K (hnmeas n) (hnbound n)).dist_le_mul f g
  have hcont := (scorePairing_lipschitz phi K hmeas hbound).continuous
  intro f
  apply (hequi f).tendsto_of_mem_closure hcont.continuousAt.continuousWithinAt
    (s := D) ?_ (hdense f)
  rintro g ⟨g', hgeq, hgc, hgs⟩
  have heqn (n : ℕ) : scorePairing (phin n) g = ∫ r, phin n r * g' r ∂mu := by
    apply integral_congr_ae
    filter_upwards [hgeq] with r hr
    rw [hr]
  have heq : scorePairing phi g = ∫ r, phi r * g' r ∂mu := by
    apply integral_congr_ae
    filter_upwards [hgeq] with r hr
    rw [hr]
  simp only [heqn, heq]
  exact hsmooth g' hgc hgs

theorem Admissible.phi_norm_bound {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), ‖d.phi r‖ ≤ (1 : ℝ) / 3 := by
  have hmem := ae_restrict_mem (μ := volume) (measurableSet_Icc (a := ell) (b := tEnd))
  filter_upwards [h.2.2.2.1, hmem] with r hphi hr
  rw [Real.norm_eq_abs, abs_of_nonneg hphi.1]
  have hlam := h.1.2
  have hrlo := hr.1
  norm_num [lambdaHi, ell] at hlam hrlo
  linarith [hphi.2]

theorem Admissible.lowPrimitive_deriv_ae {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), deriv (lowPrimitive lam d) r = d.phi r := by
  have hle : ell ≤ tEnd := by norm_num [ell, tEnd]
  have hi := (h.intervalIntegrable le_rfl hle le_rfl).ae_hasDerivAt_integral
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hi] with r hr hri
  have hd := (hr (by simpa only [uIcc_of_le hle] using hri)
    ell (by simp [uIcc_of_le hle, hle])).const_add (cap lam d.S ell)
  exact hd.deriv

/-- Integration by parts transfers testing of the measurable score to testing
its uniformly controlled primitive. -/
theorem Admissible.integral_smooth_test {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    (∫ r in ell..tEnd, d.phi r * g r) =
      g tEnd * lowPrimitive lam d tEnd - g ell * lowPrimitive lam d ell -
        ∫ r in ell..tEnd, deriv g r * lowPrimitive lam d r := by
  have hle : ell ≤ tEnd := by norm_num [ell, tEnd]
  have hJ : AbsolutelyContinuousOnInterval (lowPrimitive lam d) ell tEnd := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hle] using h.lowPrimitive_lipschitz
  have hg' : AbsolutelyContinuousOnInterval g ell tEnd :=
    ((hg.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).contDiffOn).absolutelyContinuousOnInterval
  rw [← hg'.integral_mul_deriv_eq_deriv_mul hJ]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (uIoc_subset_uIcc.trans (by rw [uIcc_of_le hle])) h.lowPrimitive_deriv_ae] with r hr
  rw [hr, mul_comm]

/-- Primitive convergence gives convergence of every smooth score test. -/
theorem smooth_tests_tendsto_of_primitive_convergence
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    Tendsto (fun n => ∫ r, (dn n).phi r * g r ∂volume.restrict (Icc ell tEnd))
      atTop (𝓝 (∫ r, d.phi r * g r ∂volume.restrict (Icc ell tEnd))) := by
  have hle : ell ≤ tEnd := by norm_num [ell, tEnd]
  have hpoint (r : ℝ) (hr : r ∈ Icc ell tEnd) :
      Tendsto (fun n => lowPrimitive (lamn n) (dn n) r) atTop (𝓝 (lowPrimitive lam d r)) :=
    hJ.tendsto_at ⟨r, hr⟩
  have hgderiv : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hint : Tendsto (fun n => ∫ r in ell..tEnd, deriv g r * lowPrimitive (lamn n) (dn n) r)
      atTop (𝓝 (∫ r in ell..tEnd, deriv g r * lowPrimitive lam d r)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun r => 3 * ‖deriv g r‖)
    · apply Eventually.of_forall
      intro n
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      exact (hgderiv.continuousOn.mul (hn n).lowPrimitive_lipschitz.continuousOn).mono
        (uIoc_subset_uIcc.trans (by rw [uIcc_of_le hle]))
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro r hr
      have hri : r ∈ Icc ell tEnd := by
        simpa only [uIcc_of_le hle] using uIoc_subset_uIcc hr
      have hbound := (hn n).lowPrimitive_range hri
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hbound.1]
      calc
        _ ≤ |deriv g r| * 3 := mul_le_mul_of_nonneg_left hbound.2 (abs_nonneg _)
        _ = _ := mul_comm _ _
    · exact (continuous_const.mul hgderiv.norm).intervalIntegrable ell tEnd
    · apply Eventually.of_forall
      intro r hr
      exact tendsto_const_nhds.mul (hpoint r
        (by simpa only [uIcc_of_le hle] using uIoc_subset_uIcc hr))
  simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  simp only [Admissible.integral_smooth_test (hn _) g hg, hd.integral_smooth_test g hg]
  exact ((tendsto_const_nhds.mul (hpoint tEnd ⟨hle, le_rfl⟩)).sub
    (tendsto_const_nhds.mul (hpoint ell ⟨le_rfl, hle⟩))).sub hint

/-- Uniform convergence of admissible primitives implies weak-star convergence
of their scores against every L¹ marginal density. -/
theorem score_tests_tendsto_of_primitive_convergence
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (g : ℝ → ℝ) (hg : Integrable g (volume.restrict (Icc ell tEnd))) :
    Tendsto (fun n => ∫ r, (dn n).phi r * g r ∂volume.restrict (Icc ell tEnd))
      atTop (𝓝 (∫ r, d.phi r * g r ∂volume.restrict (Icc ell tEnd))) := by
  have hpair := scorePairing_tendsto_of_smooth_tests
    (fun n => (dn n).phi) d.phi (1 / 3)
    (fun n => (hn n).2.2.1.aestronglyMeasurable)
    (fun n => by simpa using (hn n).phi_norm_bound)
    hd.2.2.1.aestronglyMeasurable (by simpa using hd.phi_norm_bound)
    (fun f _ hf => smooth_tests_tendsto_of_primitive_convergence lamn dn hn hd hJ f hf)
    (hg.toL1 g)
  have heqn (n : ℕ) : scorePairing (dn n).phi (hg.toL1 g) =
      ∫ r, (dn n).phi r * g r ∂volume.restrict (Icc ell tEnd) := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toL1] with r hr
    rw [hr]
  have heq : scorePairing d.phi (hg.toL1 g) =
      ∫ r, d.phi r * g r ∂volume.restrict (Icc ell tEnd) := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toL1] with r hr
    rw [hr]
  simpa only [heqn, heq] using hpair

end OptimalG.Variational
