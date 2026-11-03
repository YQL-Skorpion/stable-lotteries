import OptimalG.Certificates.VariationalBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Strict low-rank margins by convex mixing, and parameter perturbation. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

noncomputable def mixData (t : ℝ) (d e : LowRankData) : LowRankData :=
  ⟨(1 - t) * d.S + t * e.S, fun r => (1 - t) * d.phi r + t * e.phi r⟩

theorem cap_mix (lam t S T r : ℝ) :
    cap lam ((1 - t) * S + t * T) r = (1 - t) * cap lam S r + t * cap lam T r := by
  unfold cap
  ring

theorem lowPrimitive_mix {lam : ℝ} {d e : LowRankData}
    (hd : Admissible lam d) (he : Admissible lam e) (t : ℝ) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam (mixData t d e) r =
      (1 - t) * lowPrimitive lam d r + t * lowPrimitive lam e r := by
  have hdint := hd.intervalIntegrable le_rfl hr.1 hr.2
  have heint := he.intervalIntegrable le_rfl hr.1 hr.2
  unfold lowPrimitive mixData
  dsimp only
  rw [cap_mix, intervalIntegral.integral_add (hdint.const_mul (1 - t)) (heint.const_mul t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem Admissible.mix {lam : ℝ} {d e : LowRankData}
    (hd : Admissible lam d) (he : Admissible lam e) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Admissible lam (mixData t d e) := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  refine ⟨hd.1, ?_, ?_, ?_, ?_, ?_⟩
  · change (1 - t) * d.S + t * e.S ≤ slackUpper lam
    nlinarith [mul_le_mul_of_nonneg_left hd.2.1 h1t, mul_le_mul_of_nonneg_left he.2.1 ht.1]
  · exact (hd.2.2.1.const_mul (1 - t)).add (he.2.2.1.const_mul t)
  · filter_upwards [hd.2.2.2.1, he.2.2.2.1] with r hdr her
    change 0 ≤ (1 - t) * d.phi r + t * e.phi r ∧ (1 - t) * d.phi r + t * e.phi r ≤ lam - r
    constructor
    · exact add_nonneg (mul_nonneg h1t hdr.1) (mul_nonneg ht.1 her.1)
    · nlinarith [mul_le_mul_of_nonneg_left hdr.2 h1t, mul_le_mul_of_nonneg_left her.2 ht.1]
  · rw [lowPrimitive_mix hd he t (by norm_num [ell, tEnd]), hd.2.2.2.2.1, he.2.2.2.2.1]
    dsimp [mixData]
    ring
  · intro r hr
    rw [lowPrimitive_mix hd he t hr]
    change _ ≤ cap lam ((1 - t) * d.S + t * e.S) r
    rw [cap_mix]
    exact add_le_add (mul_le_mul_of_nonneg_left (hd.lowPrimitive_le_cap hr) h1t)
      (mul_le_mul_of_nonneg_left (he.lowPrimitive_le_cap hr) ht.1)

structure StrictLowMargins (lam : ℝ) (d : LowRankData) (eps : ℝ) : Prop where
  scalar : d.S + eps ≤ slackUpper lam
  score : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), eps ≤ d.phi r ∧ d.phi r ≤ lam - r - eps
  cap : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r + eps * (r - ell) ≤ Variational.cap lam d.S r

theorem slater_strict_margins {lam : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi) :
    StrictLowMargins lam (slaterData lam) (1 / 10000) := by
  have hL : lam ∈ Icc (0.562325 : ℝ) 0.562330 := by
    norm_num [lambdaLo, lambdaHi] at hl ⊢
    exact hl
  constructor
  · change (0.026 : ℝ) + 1 / 10000 ≤ slackUpper lam
    unfold slackUpper lambdaHi
    linarith [hL.1]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hr' : r ∈ Icc (0.28 : ℝ) 0.385 := by norm_num [ell, tEnd] at hr ⊢; exact hr
    have hh := Certificates.Slater.score_bounds lam r hL hr'
    change 1 / 10000 ≤ Certificates.Slater.score lam r ∧ Certificates.Slater.score lam r ≤ lam - r - 1 / 10000
    constructor <;> linarith [hh.1, hh.2]
  · intro r hr
    rw [lowPrimitive_slater]
    have hr' : r ∈ Icc (0.28 : ℝ) 0.385 := by norm_num [ell, tEnd] at hr ⊢; exact hr
    have hh := Certificates.Slater.primitive_cap_margin lam r hL hr'
    change Certificates.Slater.primitive lam r + 1 / 10000 * (r - ell) ≤ cap lam 0.026 r
    rw [certificates_cap] at hh
    dsimp [ell]
    nlinarith [hr'.1]

theorem StrictLowMargins.mix {lam eps t : ℝ} {d e : LowRankData}
    (hd : Admissible lam d) (he : Admissible lam e)
    (hm : StrictLowMargins lam e eps) (ht : t ∈ Icc (0 : ℝ) 1) :
    StrictLowMargins lam (mixData t d e) (t * eps) := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  constructor
  · change (1 - t) * d.S + t * e.S + t * eps ≤ slackUpper lam
    nlinarith [mul_le_mul_of_nonneg_left hd.2.1 h1t, mul_le_mul_of_nonneg_left hm.scalar ht.1]
  · filter_upwards [hd.2.2.2.1, hm.score] with r hdr her
    change t * eps ≤ (1 - t) * d.phi r + t * e.phi r ∧ (1 - t) * d.phi r + t * e.phi r ≤ lam - r - t * eps
    constructor
    · nlinarith [mul_nonneg h1t hdr.1, mul_le_mul_of_nonneg_left her.1 ht.1]
    · nlinarith [mul_le_mul_of_nonneg_left hdr.2 h1t, mul_le_mul_of_nonneg_left her.2 ht.1]
  · intro r hr
    rw [lowPrimitive_mix hd he t hr]
    change _ ≤ Variational.cap lam ((1 - t) * d.S + t * e.S) r
    rw [cap_mix]
    nlinarith [mul_le_mul_of_nonneg_left (hd.lowPrimitive_le_cap hr) h1t,
      mul_le_mul_of_nonneg_left (hm.cap r hr) ht.1]

theorem mixed_slater_strict {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Admissible lam (mixData t d (slaterData lam)) ∧
      StrictLowMargins lam (mixData t d (slaterData lam)) (t / 10000) := by
  refine ⟨hd.mix (slater_admissible lam hd.1) ht, ?_⟩
  simpa only [mul_one_div] using (slater_strict_margins hd.1).mix hd (slater_admissible lam hd.1) ht

noncomputable def lambdaShiftConstant (lam lam' S : ℝ) : ℝ :=
  (quadratic lam' tEnd - quadratic lam tEnd - cap lam' S ell + cap lam S ell) / (tEnd - ell)

noncomputable def lambdaShiftData (lam lam' : ℝ) (d : LowRankData) : LowRankData :=
  ⟨d.S, fun r => d.phi r + lambdaShiftConstant lam lam' d.S⟩

@[simp] theorem lambdaShiftConstant_self (lam S : ℝ) : lambdaShiftConstant lam lam S = 0 := by
  simp [lambdaShiftConstant]

theorem lambdaShiftConstant_continuous (lam S : ℝ) : Continuous (fun l => lambdaShiftConstant lam l S) := by
  unfold lambdaShiftConstant quadratic cap
  fun_prop

theorem lowPrimitive_lambdaShift {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (lam' : ℝ) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam' (lambdaShiftData lam lam' d) r =
      lowPrimitive lam d r + cap lam' d.S ell - cap lam d.S ell +
        lambdaShiftConstant lam lam' d.S * (r - ell) := by
  unfold lowPrimitive lambdaShiftData
  dsimp only
  rw [intervalIntegral.integral_add (hd.intervalIntegrable le_rfl hr.1 hr.2) intervalIntegrable_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem lambdaShift_endpoint {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) (lam' : ℝ) :
    lowPrimitive lam' (lambdaShiftData lam lam' d) tEnd = quadratic lam' tEnd - d.S := by
  rw [lowPrimitive_lambdaShift hd lam' (by norm_num [ell, tEnd]), hd.2.2.2.2.1]
  unfold lambdaShiftConstant
  rw [div_mul_cancel₀ _ (by norm_num [tEnd, ell])]
  ring

noncomputable def capSlopeFactor (S r : ℝ) : ℝ := 1 / 2 - S / ((1 - r) * (1 - ell))

theorem cap_lambda_difference (lam lam' S r : ℝ) (hr : r ≠ 1) :
    cap lam' S r - cap lam S r - (cap lam' S ell - cap lam S ell) =
      (lam' - lam) * (r - ell) * capSlopeFactor S r := by
  have hr' : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  unfold cap capSlopeFactor
  norm_num [ell]
  field_simp
  ring

theorem Admissible.capSlopeFactor_bound {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {r : ℝ} (hr : r ∈ Icc ell tEnd) : |capSlopeFactor d.S r| ≤ 1 := by
  have hs0 : 0 ≤ d.S := by linarith [hd.slack_lower]
  have hs1 := hd.slack_upper
  have hr0 := hr.1
  have hr1 := hr.2
  norm_num [ell, tEnd] at hr0 hr1
  have hden : 0 < (1 - r) * (1 - ell) := by norm_num [ell]; linarith
  have hquot0 : 0 ≤ d.S / ((1 - r) * (1 - ell)) := div_nonneg hs0 hden.le
  have hquot1 : d.S / ((1 - r) * (1 - ell)) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    norm_num [ell]
    linarith
  unfold capSlopeFactor
  rw [abs_le]
  constructor <;> linarith

theorem lambdaShift_admissible {lam eps : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hm : StrictLowMargins lam d eps) (heps : 0 < eps) {lam' : ℝ}
    (hl : lam' ∈ Icc lambdaLo lambdaHi)
    (hsmall : |lambdaShiftConstant lam lam' d.S| + |lam' - lam| ≤ eps) :
    Admissible lam' (lambdaShiftData lam lam' d) := by
  let k := lambdaShiftConstant lam lam' d.S
  have hk := le_abs_self k
  have hk' := neg_abs_le k
  have hl' := neg_abs_le (lam' - lam)
  have hksmall : |k| + |lam' - lam| ≤ eps := hsmall
  refine ⟨hl, ?_, ?_, ?_, lambdaShift_endpoint hd lam', ?_⟩
  · change d.S ≤ slackUpper lam'
    have hs := hm.scalar
    unfold slackUpper at *
    linarith [abs_nonneg k]
  · exact hd.2.2.1.add (memLp_const k)
  · filter_upwards [hm.score] with r hr
    change 0 ≤ d.phi r + k ∧ d.phi r + k ≤ lam' - r
    constructor <;> linarith [hr.1, hr.2, abs_nonneg (lam' - lam)]
  · intro r hr
    rw [lowPrimitive_lambdaShift hd lam' hr]
    have hmargin := hm.cap r hr
    have hr0 : 0 ≤ r - ell := sub_nonneg.mpr hr.1
    have hrne : r ≠ 1 := by have hh := hr.2; norm_num [tEnd] at hh; linarith
    have hid := cap_lambda_difference lam lam' d.S r hrne
    have hfactor := hd.capSlopeFactor_bound hr
    have hmabs : |(lam' - lam) * capSlopeFactor d.S r| ≤ |lam' - lam| := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor (abs_nonneg (lam' - lam))
    have hlow : -|lam' - lam| ≤ (lam' - lam) * capSlopeFactor d.S r :=
      (neg_le_neg hmabs).trans (neg_abs_le _)
    have hbound := mul_le_mul_of_nonneg_right hlow hr0
    have hsum := mul_le_mul_of_nonneg_right hksmall hr0
    have hkab := mul_le_mul_of_nonneg_right hk hr0
    change _ ≤ cap lam' d.S r
    dsimp [k] at *
    nlinarith

/-- A strict low-rank datum remains admissible under the endpoint-preserving
parameter shift, for all sufficiently close parameters inside the calibrated range. -/
theorem lambdaShift_admissible_eventually {lam eps : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hm : StrictLowMargins lam d eps) (heps : 0 < eps) :
    ∀ᶠ lam' in 𝓝 lam, lam' ∈ Icc lambdaLo lambdaHi → Admissible lam' (lambdaShiftData lam lam' d) := by
  have hcont : Continuous (fun l => |lambdaShiftConstant lam l d.S| + |l - lam|) :=
    (lambdaShiftConstant_continuous lam d.S).abs.add ((continuous_id.sub continuous_const).abs)
  have hnear : ∀ᶠ l in 𝓝 lam, |lambdaShiftConstant lam l d.S| + |l - lam| < eps := by
    apply hcont.continuousAt.eventually (gt_mem_nhds ?_)
    simpa using heps
  filter_upwards [hnear] with l hl hlrange
  exact lambdaShift_admissible hd hm heps hlrange hl.le

end OptimalG.Variational
