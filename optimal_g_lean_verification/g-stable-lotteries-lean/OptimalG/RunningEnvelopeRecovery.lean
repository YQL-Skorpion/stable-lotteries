import OptimalG.RunningEnvelope
import OptimalG.VariationalRecovery
import OptimalG.TailContact
import Mathlib.Analysis.Calculus.Monotone

/-! The repaired running envelope gives an actual measurable admissible score. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal Topology

theorem quadratic_low_monotone {lam : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi) :
    MonotoneOn (quadratic lam) (Icc ell tEnd) := by
  intro a ha b hb hab
  have hrate : 0 ≤ lam - (a + b) / 2 := by
    have hlo := hl.1
    have ha' := ha.2
    have hb' := hb.2
    norm_num [lambdaLo, tEnd] at hlo ha' hb'
    linarith
  have hh := mul_nonneg (sub_nonneg.mpr hab) hrate
  unfold quadratic
  nlinarith

theorem quadratic_low_lipschitz {lam : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi) :
    LipschitzOnWith (1 / 3 : ℝ≥0) (quadratic lam) (Icc ell tEnd) := by
  apply (convex_Icc ell tEnd).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun r _ => (quadratic_hasDerivAt lam r).hasDerivWithinAt)
  intro r hr
  apply (show (‖lam - r‖₊ : ℝ) ≤ ((1 / 3 : ℝ≥0) : ℝ) from ?_)
  change |lam - r| ≤ (1 : ℝ) / 3
  have hl0 := hl.1
  have hl1 := hl.2
  have hr0 := hr.1
  have hr1 := hr.2
  norm_num [lambdaLo, lambdaHi, ell, tEnd] at hl0 hl1 hr0 hr1
  rw [abs_le]
  constructor <;> linarith

theorem cap_low_monotone {lam S : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi)
    (hS : S ≤ slackUpper lam) : MonotoneOn (cap lam S) (Icc ell tEnd) := by
  have hlam : 0 < lam := by have hh := hl.1; norm_num [lambdaLo] at hh; linarith
  have hSup : S ≤ (26651 : ℝ) / 1000000 := by
    have hh := hl.2
    unfold slackUpper at hS
    linarith
  have hrne (r : ℝ) (hr : r ∈ Icc ell tEnd) : r ≠ 1 := by
    have hh := hr.2
    norm_num [tEnd] at hh
    linarith
  have hd (r : ℝ) (hr : r ∈ Icc ell tEnd) := cap_hasDerivAt lam S r (hrne r hr)
  apply monotoneOn_of_deriv_nonneg (convex_Icc ell tEnd)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
  intro r hr
  have hr' := interior_subset hr
  rw [(hd r hr').deriv]
  have hrt := hr'.2
  norm_num [tEnd] at hrt
  have hden : 0 < (1 - r) ^ 2 := sq_pos_of_pos (by linarith)
  have hq : S / (1 - r) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (r - 0.385)]
  have hm := mul_nonneg hlam.le (show 0 ≤ 1 / 2 - S / (1 - r) ^ 2 by linarith)
  unfold capScore
  simpa only [mul_sub, ← mul_div_assoc, mul_one] using hm

/-- All low-rank admissibility obligations for the B.1 envelope are discharged
from properties of the original primitive and its cap. -/
theorem admissible_runningEnvelope {lam S : ℝ} {J : ℝ → ℝ}
    (hl : lam ∈ Icc lambdaLo lambdaHi) (hS : S ≤ slackUpper lam)
    (hc : ContinuousOn J (Icc ell tEnd))
    (hinc : ∀ x ∈ Icc ell tEnd, ∀ y ∈ Icc ell tEnd, x ≤ y →
      J y - J x ≤ quadratic lam y - quadratic lam x)
    (hcap : ∀ r ∈ Icc ell tEnd, J r ≤ cap lam S r)
    (hend : J tEnd = quadratic lam tEnd - S)
    (hfloor : cap lam S ell ≤ J tEnd)
    (hdom : ∀ r ∈ Icc ell tEnd, J r ≤ J tEnd) :
    let E := runningEnvelope J ell (cap lam S ell)
    Admissible lam ⟨S, deriv E⟩ ∧
      (∀ r ∈ Icc ell tEnd, lowPrimitive lam ⟨S, deriv E⟩ r = E r) ∧
      (∀ r ∈ Icc ell tEnd, J r ≤ E r) := by
  let E := runningEnvelope J ell (cap lam S ell)
  have hLip := runningEnvelope_lipschitz hc (quadratic_low_monotone hl) (quadratic_low_lipschitz hl)
    hinc (floor := cap lam S ell)
  have hleft : E ell = cap lam S ell := by
    have hh := hcap ell (by norm_num [ell, tEnd])
    simp only [E, runningEnvelope, Icc_self, image_singleton, csSup_singleton, max_eq_left hh]
  have hright : E tEnd = quadratic lam tEnd - S := by
    exact (runningEnvelope_endpoint (by norm_num [ell, tEnd]) hfloor hdom).trans hend
  have hEc : ∀ r ∈ Icc ell tEnd, E r ≤ cap lam S r :=
    fun r hr => runningEnvelope_cap hc (cap_low_monotone hl hS) le_rfl hcap hr
  have hm := runningEnvelope_monotone hc (floor := cap lam S ell)
  have hs : MonotoneOn (fun r => quadratic lam r - E r) (Icc ell tEnd) := by
    intro x hx y hy hxy
    have hh := (runningEnvelope_increment hc (quadratic_low_monotone hl) hinc hx hy hxy
      (floor := cap lam S ell)).2
    change E y - E x ≤ _ at hh
    linarith
  obtain ⟨had, hrec⟩ := admissible_of_primitive lam S E hl hS hLip hleft hright hEc hm hs
  refine ⟨had, hrec, ?_⟩
  intro r hr
  exact runningEnvelope_dominates hc hr ⟨hr.1, le_rfl⟩

/-- The recovered score keeps the old derivative wherever it is nonzero,
outside a null set. -/
theorem runningEnvelope_score_selection {J phi : ℝ → ℝ} {a b floor : ℝ}
    (hc : ContinuousOn J (Icc a b))
    (hphi : ∀ r ∈ Ioo a b, HasDerivAt J (phi r) r) :
    ∀ᵐ r ∂volume.restrict (Icc a b),
      deriv (runningEnvelope J a floor) r = 0 ∨ deriv (runningEnvelope J a floor) r = phi r := by
  have hdiff := (runningEnvelope_monotone hc (floor := floor)).ae_differentiableWithinAt_of_mem
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hdiff] with r hr hri
  have hwithin := hr ⟨hri.1.le, hri.2.le⟩
  have hderiv := (hwithin.differentiableAt (Icc_mem_nhds hri.1 hri.2)).hasDerivAt
  exact runningEnvelope_derivative_selection hc hri (hphi r hri) hderiv

/-- Piecewise modifications need only an almost-everywhere derivative. This
version includes the finitely many joins introduced by slack removal. -/
theorem runningEnvelope_score_selection_ae {J phi : ℝ → ℝ} {a b floor : ℝ}
    (hc : ContinuousOn J (Icc a b))
    (hphi : ∀ᵐ r ∂volume.restrict (Icc a b), HasDerivAt J (phi r) r) :
    ∀ᵐ r ∂volume.restrict (Icc a b),
      deriv (runningEnvelope J a floor) r = 0 ∨ deriv (runningEnvelope J a floor) r = phi r := by
  have hi : ∀ᵐ r ∂volume.restrict (Icc a b), r ∈ Ioo a b := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hd := (runningEnvelope_monotone hc (floor := floor)).ae_differentiableWithinAt_of_mem
  have hdr : ∀ᵐ r ∂volume.restrict (Icc a b),
      r ∈ Icc a b → DifferentiableWithinAt ℝ (runningEnvelope J a floor) (Icc a b) r :=
    ae_restrict_of_ae hd
  filter_upwards [hphi, hi, hdr] with r hpr hr hdr
  have hwithin := hdr ⟨hr.1.le, hr.2.le⟩
  have hderiv := (hwithin.differentiableAt (Icc_mem_nhds hr.1 hr.2)).hasDerivAt
  exact runningEnvelope_derivative_selection hc hr hpr hderiv

end OptimalG.Variational
