import OptimalG.SplitBounds

/-! Exact coefficient continuation above p_+ in C.23. -/
namespace OptimalG
open Set

noncomputable def extendedDenom (lam p t R P : ℝ) : ℝ :=
  (lam - t) * R + (lam - p) * P
noncomputable def extendedBeta (lam p t R P : ℝ) : ℝ :=
  (lam ^ 2 - t * p) / extendedDenom lam p t R P
noncomputable def extendedEta (lam p t R P : ℝ) : ℝ :=
  ((2 * lam - t) * R - (2 * p - lam) * P) / extendedDenom lam p t R P

theorem extended_coefficients_system (lam p t R P : ℝ)
    (hN : extendedDenom lam p t R P ≠ 0) :
    extendedBeta lam p t R P * P + extendedEta lam p t R P * (lam - t) = 2 * lam - t ∧
    extendedBeta lam p t R P * R - extendedEta lam p t R P * (lam - p) = 2 * p - lam := by
  unfold extendedBeta extendedEta
  constructor <;> field_simp <;> unfold extendedDenom <;> ring

theorem extendedDenom_pos {lam p t R P : ℝ}
    (ht : t < lam) (hp : p ≤ lam) (hR : 0 < R) (hP : 0 ≤ P) :
    0 < extendedDenom lam p t R P :=
  add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) hR) (mul_nonneg (sub_nonneg.mpr hp) hP)

theorem extendedBeta_pos {lam p t R P : ℝ}
    (hl : 0 < lam) (ht : t ∈ Ico (0 : ℝ) lam) (hp : p ≤ lam)
    (hR : 0 < R) (hP : 0 ≤ P) : 0 < extendedBeta lam p t R P := by
  have hm := mul_le_mul_of_nonneg_left hp ht.1
  have hn : 0 < lam ^ 2 - t * p := by nlinarith [mul_pos hl (sub_pos.mpr ht.2)]
  exact div_pos hn (extendedDenom_pos ht.2 hp hR hP)

theorem extendedEta_ge_one {lam p t R P : ℝ}
    (hN : 0 < extendedDenom lam p t R P) (hbin : p * P ≤ lam * R) :
    1 ≤ extendedEta lam p t R P := by
  unfold extendedEta
  rw [le_div_iff₀ hN]
  unfold extendedDenom
  nlinarith

/-- A supporting line at eta0 transfers to every smaller coefficient eta≥1,
with the ceiling taking over above its crossing rank. -/
theorem supporting_line_transfer {phi : ℝ → ℝ} {lam t eta eta0 : ℝ}
    (heta : 1 ≤ eta) (heta0 : eta ≤ eta0)
    (hcap : ∀ x ∈ Icc (0 : ℝ) lam, phi x ≤ lam - x)
    (hsupport : ∀ x ∈ Icc (0 : ℝ) lam,
      x + eta0 * phi x ≤ eta0 * lam - (eta0 - 1) * t) :
    ∀ x ∈ Icc (0 : ℝ) lam, x + eta * phi x ≤ eta * lam - (eta - 1) * t := by
  intro x hx
  by_cases hxt : x ≤ t
  · by_cases hd : 0 ≤ phi x - lam + t
    · have hm := mul_le_mul_of_nonneg_right heta0 hd
      have hs := hsupport x hx
      nlinarith
    · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ eta by linarith) (le_of_not_ge hd)
      nlinarith
  · have hm := mul_le_mul_of_nonneg_left (hcap x hx) (show 0 ≤ eta by linarith)
    have hn := mul_nonneg (sub_nonneg.mpr heta) (show 0 ≤ x - t by linarith)
    nlinarith

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem extended_supports {p t R P eta0 : ℝ}
    (hp : p ≤ lam) (hN : extendedDenom lam p t R P ≠ 0)
    (heta : 1 ≤ extendedEta lam p t R P) (heta0 : extendedEta lam p t R P ≤ eta0)
    (hline : ∀ y ∈ Icc p lam, phi y = lam - y)
    (hsupport : ∀ x ∈ Icc (0 : ℝ) lam,
      x + eta0 * phi x ≤ eta0 * lam - (eta0 - 1) * t) :
    (∀ x ∈ Icc (0 : ℝ) lam,
      x + extendedEta lam p t R P * phi x ≤ 2 * lam - extendedBeta lam p t R P * P) ∧
    (∀ y ∈ Icc p lam,
      y + extendedEta lam p t R P * phi y ≤ lam - p + extendedBeta lam p t R P * R) := by
  have hs := extended_coefficients_system lam p t R P hN
  constructor
  · intro x hx
    have hh := supporting_line_transfer heta heta0
      (fun r hr => h.ceiling r ⟨hr.1, hr.2.trans h.lam_lt_one.le⟩) hsupport x hx
    linarith [hs.1]
  · intro y hy
    rw [hline y hy]
    have hm := mul_nonneg (show 0 ≤ extendedEta lam p t R P - 1 by linarith)
      (sub_nonneg.mpr hy.1)
    nlinarith [hs.2]

theorem thirdTest_fullSplit_of_system {p beta eta : ℝ}
    (hp : p ≤ lam) (heta : 1 ≤ eta)
    (hsystem : beta * curvePrimitive phi p - eta * (lam - p) = 2 * p - lam) :
    ∀ z ∈ Icc lam 1,
      z + p - lam + beta * packingK phi p p z + eta * phi z ≤ 0 := by
  intro z hz
  have hm := mul_le_mul_of_nonneg_left
    (h.ceiling z ⟨h.lam_pos.le.trans hz.1, hz.2⟩) (show 0 ≤ eta by linarith)
  have hn := mul_nonneg (show 0 ≤ eta - 1 by linarith) (show 0 ≤ z - p by linarith [hz.1])
  have heq : packingK phi p p z = -curvePrimitive phi p := by
    unfold packingK
    rw [sub_add_cancel]
    ring
  rw [heq]
  nlinarith

end VerifierCurve
end OptimalG
