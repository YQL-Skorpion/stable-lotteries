import OptimalG.ConcaveIncrements
import OptimalG.NormalizedVerifier

/-! Sufficient all-split verifier conditions for masses above λ. -/
namespace OptimalG
open Set

structure HighMassTest (phi : ℝ → ℝ) (lam p beta : ℝ) (corr : ℝ → ℝ) : Prop where
  beta_nonneg : 0 ≤ beta
  corr_nonneg : ∀ x ∈ Ico (0 : ℝ) lam, 0 ≤ corr x
  normalized : beta * curvePrimitive phi p = p
  low_first : ∀ x ∈ Ico (0 : ℝ) lam, ∀ q, 0 ≤ q → q ≤ x →
    q + beta * packingDelta phi p q + corr x ≤ lam
  binary : ∀ q ∈ Icc (0 : ℝ) lam, q + beta * packingDelta phi p q ≤ lam
  ratio : ∀ x ∈ Ico (0 : ℝ) lam,
    lowRankRatio phi lam x - correctionRatio phi (corr x) x ≤ beta * (1 - p)
  mixed : ∀ x ∈ Ico (0 : ℝ) lam, ∀ q ∈ Icc (0 : ℝ) lam, ∀ z ∈ Icc p 1,
    z + q - lam + beta * packingK phi p q z +
      (lowRankRatio phi lam x + correctionRatio phi (corr x) x) * phi z ≤ 0

theorem highMassTest_verifier {phi : ℝ → ℝ} {lam p beta : ℝ} {corr : ℝ → ℝ}
    (h : VerifierCurve phi lam) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p ∈ Ioo lam 1) (ht : HighMassTest phi lam p beta corr) :
    VerifierOn {p} phi lam (fun _ => beta) (fun _ x => corr x) := by
  constructor
  · intro r hr; exact ht.beta_nonneg
  · intro r hr x hx; exact ht.corr_nonneg x hx
  · intro r hr x hx q hq hqr hqx
    have hrp : r = p := hr
    subst r
    exact ht.low_first x hx q hq hqx
  · intro r hr x hx q hq hqr hrx
    have hrp : r = p := hr
    exfalso
    linarith [hp.1, hx.2]
  · intro r hr x hx q hq hqr
    have hrp : r = p := hr
    subst r
    by_cases hql : q ≤ lam
    · exact (normalized_high_first_low h hx ⟨hq, hql⟩).mpr (ht.binary q ⟨hq, hql⟩)
    · apply (normalized_high_first_high h hx ⟨lt_of_not_ge hql, hqr.trans hp.2.le⟩).mpr
      have hd := mul_le_mul_of_nonneg_left
        (h.packingDelta_le_score ⟨h.lam_pos.le.trans hp.1.le, hp.2.le⟩ hq hqr) ht.beta_nonneg
      have hr := mul_le_mul_of_nonneg_right (ht.ratio x hx)
        (neg_nonneg.mpr (h.nonpositive ⟨le_of_not_ge hql, hqr.trans hp.2.le⟩))
      nlinarith
  · intro r hr x hx q z hq hqr hrz hz
    have hrp : r = p := hr
    subst r
    have hlz : lam < z := hp.1.trans_le hrz
    by_cases hql : q ≤ lam
    · exact (normalized_high_second_mixed h hx hql ⟨hlz, hz⟩).mpr
        (ht.mixed x hx q ⟨hq, hql⟩ z ⟨hrz, hz⟩)
    · apply (normalized_high_second_high h hx (lt_of_not_ge hql) ⟨hlz, hz⟩).mpr
      apply highSplit_reduction h hc p q z beta (lowRankRatio phi lam x)
        (correctionRatio phi (corr x) x) (le_of_not_ge hql) hqr hrz hz ht.beta_nonneg
      · exact potential_ratio_ge_one phi lam x (h.positive hx)
          (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
      · exact div_nonneg (ht.corr_nonneg x hx) (h.positive hx).le
      · exact ht.normalized
      · have hb := ht.mixed x hx lam ⟨h.lam_pos.le, le_rfl⟩ z ⟨hrz, hz⟩
        rw [h.at_lam]
        linarith

noncomputable def largeMassCorrection (phi : ℝ → ℝ) (lam p beta x : ℝ) : ℝ :=
  max (lam - x - beta * (1 - p) * phi x) 0

theorem largeMassCorrection_ratio {phi : ℝ → ℝ} {lam p beta x : ℝ}
    (h : VerifierCurve phi lam) (hx : x ∈ Ico (0 : ℝ) lam) :
    lowRankRatio phi lam x - correctionRatio phi (largeMassCorrection phi lam p beta x) x ≤ beta * (1 - p) := by
  have hc : lam - x - beta * (1 - p) * phi x ≤ largeMassCorrection phi lam p beta x := le_max_left _ _
  unfold lowRankRatio correctionRatio
  rw [← sub_div, div_le_iff₀ (h.positive hx)]
  linarith

/-- The large-mass construction reduces all remaining high-rank checks to coefficient one. -/
theorem highMassTest_largeCorrection {phi : ℝ → ℝ} {lam p : ℝ}
    (h : VerifierCurve phi lam) (hp : p ∈ Ioo lam 1)
    (hfirst : ∀ x ∈ Ico (0 : ℝ) lam, ∀ q, 0 ≤ q → q ≤ x →
      q + (p / curvePrimitive phi p) * packingDelta phi p q +
        largeMassCorrection phi lam p (p / curvePrimitive phi p) x ≤ lam)
    (hbinary : ∀ q ∈ Icc (0 : ℝ) lam,
      q + (p / curvePrimitive phi p) * packingDelta phi p q ≤ lam)
    (hmixed : ∀ q ∈ Icc (0 : ℝ) lam, ∀ z ∈ Icc p 1,
      z + q - lam + (p / curvePrimitive phi p) * packingK phi p q z + phi z ≤ 0) :
    HighMassTest phi lam p (p / curvePrimitive phi p)
      (largeMassCorrection phi lam p (p / curvePrimitive phi p)) := by
  have hp0 : 0 < p := h.lam_pos.trans hp.1
  have hJ := h.primitive_pos ⟨hp0, hp.2⟩
  constructor
  · exact (div_pos hp0 hJ).le
  · intro x hx; exact le_max_right _ _
  · exact div_mul_cancel₀ p (ne_of_gt hJ)
  · exact hfirst
  · exact hbinary
  · intro x hx; exact largeMassCorrection_ratio h hx
  · intro x hx q hq z hz
    have hr := potential_ratio_ge_one phi lam x (h.positive hx)
      (h.ceiling x ⟨hx.1, hx.2.le.trans h.lam_lt_one.le⟩)
    have hu : 0 ≤ correctionRatio phi (largeMassCorrection phi lam p (p / curvePrimitive phi p) x) x :=
      div_nonneg (le_max_right _ _) (h.positive hx).le
    have hratio : 1 ≤ lowRankRatio phi lam x +
        correctionRatio phi (largeMassCorrection phi lam p (p / curvePrimitive phi p) x) x := by
      change 1 ≤ (lam - x) / phi x + _
      linarith
    have hm := mul_le_mul_of_nonpos_right hratio (h.nonpositive ⟨hp.1.le.trans hz.1, hz.2⟩)
    have hb := hmixed q hq z hz
    linarith

end OptimalG
