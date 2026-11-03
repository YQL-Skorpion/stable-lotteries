import OptimalG.SlackRemoval
import OptimalG.UniversalControlBoxes

/-! Concrete primitives realizing the two calibrated slack-removal phases. -/
namespace OptimalG.Relocation
open Set

noncomputable def slack (lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  clippedActivation (cumulativeSlack lam phi)
noncomputable def massOne (lam : ℝ) (phi : ℝ → ℝ) : ℝ := slack lam phi 0.44-slack lam phi 0.38
noncomputable def massTwo (lam : ℝ) (phi : ℝ → ℝ) : ℝ := slack lam phi 0.775-slack lam phi 0.44
noncomputable def prefixGain (lam : ℝ) (phi : ℝ → ℝ) : ℝ := 2.98*massOne lam phi
noncomputable def fraction (lam : ℝ) (phi : ℝ → ℝ) : ℝ := prefixGain lam phi/slack lam phi 0.245
noncomputable def firstSlack (lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  flattenSlack (drainSlack (slack lam phi) 0.245 (fraction lam phi)) 0.38 0.44
noncomputable def secondSlack (lam : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  flattenSlack (firstSlack lam phi) 0.44 0.775
noncomputable def firstPrimitive (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  linePrimitive lam r-firstSlack lam phi r
noncomputable def secondPrimitive (lam : ℝ) (phi : ℝ → ℝ) (r : ℝ) : ℝ :=
  linePrimitive lam r-secondSlack lam phi r

theorem slack_eq (lam : ℝ) (phi : ℝ → ℝ) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    slack lam phi r = cumulativeSlack lam phi r := clippedActivation_eq _ _ hr

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem slack_monotone : Monotone (slack lam phi) := by
  intro r s hrs
  apply h.cumulativeSlack_mono
  · exact le_max_left _ _
  · exact max_le_max le_rfl (min_le_min_left 1 hrs)
  · exact max_le (by norm_num) (min_le_left _ _)

theorem slack_nonneg (r : ℝ) : 0 ≤ slack lam phi r :=
  h.cumulativeSlack_nonneg ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem mass_budget (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    0 ≤ massOne lam phi ∧ 0 ≤ massTwo lam phi ∧
      massOne lam phi+massTwo lam phi < (0.00025509854 : ℝ) := by
  have hm1 := (slack_monotone h) (by norm_num : (0.38 : ℝ) ≤ 0.44)
  have hm2 := (slack_monotone h) (by norm_num : (0.44 : ℝ) ≤ 0.775)
  have ha := (slack_monotone h) (by norm_num : (0.345 : ℝ) ≤ 0.38)
  have hb := (slack_monotone h) (by norm_num : (0.775 : ℝ) ≤ 0.785)
  have hc := h.central_slack_bound hL hLP
  rw [h.slack_integral (by norm_num) (by norm_num) (by norm_num)] at hc
  have hea := slack_eq lam phi (r := 0.345) (by norm_num)
  have heb := slack_eq lam phi (r := 0.785) (by norm_num)
  unfold massOne massTwo
  constructor
  · linarith
  constructor <;> linarith

theorem prefix_available (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : (0.014975 : ℝ) < slack lam phi 0.245 := by
  rw [slack_eq lam phi (by norm_num)]
  exact h.available_low_slack hL hLP

theorem fraction_mem (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : fraction lam phi ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hm1,hm2,hmt⟩ := (mass_budget h) hL hLP
  have ha := (prefix_available h) hL hLP
  have ha0 : 0 < slack lam phi 0.245 := by linarith
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) hm1) ha0.le
  · unfold fraction prefixGain
    rw [div_le_iff₀ ha0]
    nlinarith only [hm2,hmt,ha]

theorem fraction_mul_prefix (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    fraction lam phi*slack lam phi 0.245 = prefixGain lam phi := by
  unfold fraction
  exact div_mul_cancel₀ _ (ne_of_gt (lt_trans (by norm_num) ((prefix_available h) hL hLP)))

theorem first_monotone (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : Monotone (firstSlack lam phi) :=
  flattenSlack_monotone (drainSlack_monotone (slack_monotone h) ((fraction_mem h) hL hLP) _) _ _

theorem second_monotone (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) : Monotone (secondSlack lam phi) :=
  flattenSlack_monotone ((first_monotone h) hL hLP) _ _

theorem first_low_eq (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ∈ Icc (0.245 : ℝ) 0.38) :
    firstSlack lam phi r = slack lam phi r-prefixGain lam phi := by
  rw [firstSlack, (first_phase_exact (slack_monotone h) ((fraction_mem h) hL hLP)
    (by norm_num : (0.245 : ℝ) ≤ 0.38) (by norm_num : (0.38 : ℝ) ≤ 0.44)).1 hr,
    (fraction_mul_prefix h) hL hLP]

theorem first_after_eq (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : 0.44 ≤ r) :
    firstSlack lam phi r = slack lam phi r-prefixGain lam phi-massOne lam phi := by
  rw [firstSlack, (first_phase_exact (slack_monotone h) ((fraction_mem h) hL hLP)
    (by norm_num : (0.245 : ℝ) ≤ 0.38) (by norm_num : (0.38 : ℝ) ≤ 0.44)).2 hr,
    (fraction_mul_prefix h) hL hLP]
  rfl

theorem first_gain_bounds (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : 0.245 ≤ r) :
    prefixGain lam phi ≤ slack lam phi r-firstSlack lam phi r ∧
      slack lam phi r-firstSlack lam phi r ≤ prefixGain lam phi+massOne lam phi := by
  have hd := drainSlack_monotone (slack_monotone h) ((fraction_mem h) hL hLP) (0.245 : ℝ)
  have hb := flattenSlack_bounds hd (by norm_num : (0.38 : ℝ) ≤ 0.44) r
  rw [drainSlack_eq_after (slack_monotone h) hr,
    drainSlack_eq_after (slack_monotone h) (by norm_num : (0.245 : ℝ) ≤ 0.44),
    drainSlack_eq_after (slack_monotone h) (by norm_num : (0.245 : ℝ) ≤ 0.38),
    (fraction_mul_prefix h) hL hLP] at hb
  change _ ≤ firstSlack lam phi r ∧ firstSlack lam phi r ≤ _ at hb
  unfold massOne
  constructor <;> linarith [hb.1,hb.2]

theorem second_gain_bounds (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) (r : ℝ) :
    0 ≤ firstSlack lam phi r-secondSlack lam phi r ∧
      firstSlack lam phi r-secondSlack lam phi r ≤ massTwo lam phi := by
  have hb := flattenSlack_bounds ((first_monotone h) hL hLP)
    (by norm_num : (0.44 : ℝ) ≤ 0.775) r
  rw [(first_after_eq h) hL hLP (by norm_num : (0.44 : ℝ) ≤ 0.775),
    (first_after_eq h) hL hLP (by norm_num : (0.44 : ℝ) ≤ 0.44)] at hb
  change _ ≤ secondSlack lam phi r ∧ secondSlack lam phi r ≤ _ at hb
  unfold massTwo
  constructor <;> linarith [hb.1,hb.2]

theorem second_low_eq (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {r : ℝ} (hr : r ≤ 0.44) :
    secondSlack lam phi r = firstSlack lam phi r :=
  flattenSlack_eq_before ((first_monotone h) hL hLP) (by norm_num) hr

/-- The first phase has exactly the prescribed R and P increments. -/
theorem first_RP_increments (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {p : ℝ} (hp : p ∈ Icc (0.25 : ℝ) 0.36) :
    firstPrimitive lam phi p = activationPrimitive phi p+prefixGain lam phi ∧
    firstPrimitive lam phi (1-p) = activationPrimitive phi (1-p)+prefixGain lam phi+massOne lam phi := by
  have hpeq : slack lam phi p = linePrimitive lam p-activationPrimitive phi p :=
    slack_eq lam phi ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hceq : slack lam phi (1-p) = linePrimitive lam (1-p)-activationPrimitive phi (1-p) :=
    slack_eq lam phi ⟨by linarith [hp.2],by linarith [hp.1]⟩
  constructor
  · rw [firstPrimitive,(first_low_eq h) hL hLP ⟨by linarith [hp.1],by linarith [hp.2]⟩,hpeq]
    ring
  · rw [firstPrimitive,(first_after_eq h) hL hLP (by linarith [hp.2]),hceq]
    ring

end OptimalG.Relocation
