import OptimalG.PhaseControlBounds
import OptimalG.ClippedDerivative

/-! Finite clipped-control comparison for the two slack-relocation phases. -/
namespace OptimalG.Certificates.Control
open Set
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

noncomputable def phaseValue (U h k R P K A B eta dp dk mu err t : ℝ) : ℝ :=
  value U h k (R + t * eta) (P + t * (eta + dp)) (K + t * (dk - mu + err)) A B

noncomputable def phaseSlope (U h k R P K A B eta dp dk mu err t : ℝ) : ℝ :=
  let Rt := R + t * eta
  let Pt := P + t * (eta + dp)
  let Kt := K + t * (dk - mu + err)
  let D := det h k Rt Pt
  let M := alphaNumerator h k A B
  M * (cy U h Pt Kt - cx U k Rt Kt) / D ^ 2 * eta -
    M * cx U k Rt Kt / D ^ 2 * dp + M / D * (mu - dk - err)

theorem phaseValue_hasDerivAt (U h k R P K A B eta dp dk mu err t : ℝ)
    (hD : det h k (R + t * eta) (P + t * (eta + dp)) ≠ 0) :
    HasDerivAt (phaseValue U h k R P K A B eta dp dk mu err)
      (phaseSlope U h k R P K A B eta dp dk mu err t) t := by
  have hR := ((hasDerivAt_id t).mul_const eta).const_add R
  have hP := ((hasDerivAt_id t).mul_const (eta + dp)).const_add P
  have hK := ((hasDerivAt_id t).mul_const (dk - mu + err)).const_add K
  have hnum := (((hR.mul_const A).add (hP.mul_const B)).const_mul U).add
    (hK.mul_const (alphaNumerator h k A B))
  have hden := (hR.const_mul h).sub (hP.const_mul k)
  have hh := hnum.neg.div hden hD
  convert hh using 1 <;> first | rfl | skip
  simp only [id_eq, one_mul]
  unfold phaseSlope
  dsimp only
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
  generalize R + t * eta = Rt at *
  generalize P + t * (eta + dp) = Pt at *
  generalize K + t * (dk - mu + err) = Kt at *
  change _ = (-(U * (eta * A + (eta + dp) * B) + (dk - mu + err) * alphaNumerator h k A B) * det h k Rt Pt -
    -(U * (Rt * A + Pt * B) + Kt * alphaNumerator h k A B) * (h * eta - k * (eta + dp))) / (det h k Rt Pt) ^ 2
  field_simp [hD]
  unfold det cx cy alphaNumerator
  ring

theorem phaseSlope_lower {U h k R P K A B eta dp dk mu err t : ℝ}
    (heta : 0 ≤ eta) (hmu : 0 ≤ mu) (herr : 0 ≤ err)
    (hdp : dp ≤ mu) (hdk : dk ≤ mu)
    (hD : 0 < det h k (R + t * eta) (P + t * (eta + dp)))
    (hM : 0 ≤ alphaNumerator h k A B)
    (hX : 0 ≤ cx U k (R + t * eta) (K + t * (dk - mu + err)))
    (hXY : cx U k (R + t * eta) (K + t * (dk - mu + err)) ≤
      cy U h (P + t * (eta + dp)) (K + t * (dk - mu + err)))
    (hAlpha : alphaNumerator h k A B / det h k (R + t * eta) (P + t * (eta + dp)) ≤ 4.53)
    (hLoss : alphaNumerator h k A B * cx U k (R + t * eta) (K + t * (dk - mu + err)) /
      (det h k (R + t * eta) (P + t * (eta + dp))) ^ 2 ≤ 6.19) :
    -(6.19 * mu + 4.53 * err) ≤ phaseSlope U h k R P K A B eta dp dk mu err t := by
  let D := det h k (R + t * eta) (P + t * (eta + dp))
  let M := alphaNumerator h k A B
  let X := cx U k (R + t * eta) (K + t * (dk - mu + err))
  let Y := cy U h (P + t * (eta + dp)) (K + t * (dk - mu + err))
  have hterm : 0 ≤ M * (Y - X) / D ^ 2 * eta :=
    mul_nonneg (div_nonneg (mul_nonneg hM (sub_nonneg.mpr hXY)) (sq_nonneg _)) heta
  have hcp : 0 ≤ M * X / D ^ 2 := div_nonneg (mul_nonneg hM hX) (sq_nonneg _)
  have ha : 0 ≤ M / D := div_nonneg hM hD.le
  have hdp' := mul_le_mul_of_nonneg_left hdp hcp
  have hLoss' := mul_le_mul_of_nonneg_right hLoss hmu
  have hdk' := mul_nonneg ha (sub_nonneg.mpr hdk)
  have hAlpha' := mul_le_mul_of_nonneg_right hAlpha herr
  change -(6.19 * mu + 4.53 * err) ≤ M * (Y - X) / D ^ 2 * eta - M * X / D ^ 2 * dp + M / D * (mu - dk - err)
  change M * X / D ^ 2 * mu ≤ 6.19 * mu at hLoss'
  change M / D * err ≤ 4.53 * err at hAlpha'
  nlinarith

/-- The active derivative bounds imply the finite phase comparison even when
the minimizing branch crosses the straight-line control during interpolation. -/
theorem phaseValue_clipped_comparison (U h k R P K A B eta dp dk mu err : ℝ)
    (hmu : 0 ≤ mu) (herr : 0 ≤ err)
    (hD : ∀ t ∈ Icc (0 : ℝ) 1, det h k (R + t * eta) (P + t * (eta + dp)) ≠ 0)
    (hactive : ∀ t ∈ Ico (0 : ℝ) 1,
      phaseValue U h k R P K A B eta dp dk mu err t ≤ -U →
      -(6.19 * mu + 4.53 * err) ≤ phaseSlope U h k R P K A B eta dp dk mu err t) :
    min (-U) (value U h k R P K A B) - (6.19 * mu + 4.53 * err) ≤
      min (-U) (value U h k (R + eta) (P + eta + dp) (K + dk - mu + err) A B) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    phaseValue_hasDerivAt U h k R P K A B eta dp dk mu err t (hD t ht)
  have hh := clipped_decrease_of_active_derivative
    (phaseValue U h k R P K A B eta dp dk mu err)
    (phaseSlope U h k R P K A B eta dp dk mu err) 0 1 (-U) (6.19 * mu + 4.53 * err)
    (by positivity) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) hactive 1 (by norm_num)
  simpa only [phaseValue, zero_mul, add_zero, one_mul, sub_zero, mul_one, add_assoc, add_sub_assoc] using hh

/-- The calibrated phase comparison with all derivative hypotheses discharged
from the numerical rectangle, the two binary inequalities, and score ceilings. -/
theorem phaseValue_clipped_of_geometry {L p x y U R P K A B eta dp dk mu err : ℝ}
    (hL : Compact.LambdaRange L) (hp : p ∈ Icc (0.25 : ℝ) 0.36)
    (hx : x ∈ Icc (0.285 : ℝ) 0.38) (hy : y ∈ Icc (0.285 : ℝ) 0.38)
    (hpy : p ≤ y) (hU : U ∈ Icc (0.21267 : ℝ) 0.313)
    (hA : A ≤ L - x) (hB : B ≤ L - y)
    (heta : 0 ≤ eta) (hmu : 0 ≤ mu) (herr : 0 ≤ err)
    (hdp : dp ≤ mu) (hdk : dk ≤ mu)
    (hgeo : ∀ t ∈ Icc (0 : ℝ) 1,
      let Rt := R + t * eta
      let Pt := P + t * (eta + dp)
      let Kt := K + t * (dk - mu + err)
      Rt ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ Pt ∧ Kt ∈ Icc (0 : ℝ) 0.159 ∧
      0.0519 < det (2 * L - x) (p + y - L) Rt Pt ∧
      0 < cx U (p + y - L) Rt Kt ∧
      0 < L * Rt - p * Pt ∧ (1 - p) * Rt ≤ L * Pt) :
    min (-U) (value U (2 * L - x) (p + y - L) R P K A B) -
        (6.19 * mu + 4.53 * err) ≤
      min (-U) (value U (2 * L - x) (p + y - L) (R + eta)
        (P + eta + dp) (K + dk - mu + err) A B) := by
  apply phaseValue_clipped_comparison _ _ _ _ _ _ _ _ _ _ _ _ _ hmu herr
  · intro t ht
    exact ne_of_gt (lt_trans (by norm_num) (hgeo t ht).2.2.2.1)
  · intro t ht hactive
    obtain ⟨hR, hP, hK, hD, hX, hbinary, hbinary'⟩ := hgeo t ⟨ht.1, ht.2.le⟩
    have hD0 : 0 < det (2 * L - x) (p + y - L)
        (R + t * eta) (P + t * (eta + dp)) := lt_trans (by norm_num) hD
    have hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU.1
    have hR0 : 0 ≤ R + t * eta := le_trans (by norm_num) hR.1
    have hM := active_alpha_positive U (2 * L - x) (p + y - L)
      (R + t * eta) (P + t * (eta + dp)) (K + t * (dk - mu + err)) A B
      hU0 hD0 hK.1 (score_gap L p x y _ _ A B hR0 hP hA hB hbinary) hactive
    have hRP : R + t * eta ≤ P + t * (eta + dp) := by
      have hcoef : L < 1 - p := by linarith [hL.2, hp.2]
      have hL0 : 0 < L := by linarith [hL.1]
      nlinarith
    have hhk : 0 ≤ (2 * L - x) - (p + y - L) := by
      linarith [hL.1, hx.2, hy.2, hp.2]
    have hXY : cx U (p + y - L) (R + t * eta) (K + t * (dk - mu + err)) ≤
        cy U (2 * L - x) (P + t * (eta + dp)) (K + t * (dk - mu + err)) := by
      have h1 := mul_nonneg hU0.le (sub_nonneg.mpr hRP)
      have h2 := mul_nonneg hhk hK.1
      unfold cx cy
      nlinarith
    have hb := active_phase_slopes hL hp hx hy hpy hU hR hK hD hX hA hB hactive
    exact phaseSlope_lower heta hmu herr hdp hdk hD0 hM.le hX.le hXY hb.1.le hb.2.le

end OptimalG.Certificates.Control
