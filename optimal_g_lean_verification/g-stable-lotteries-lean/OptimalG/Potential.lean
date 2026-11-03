import Mathlib.Tactic

/-!
# The individual potential from (5.6)

The derivative hypothesis is used here in its integrated form: the decrease of `phi`
between high ranks is at least the increase in rank. Deriving this from absolute
continuity and the almost-everywhere derivative bound is a separate obligation.
-/

namespace OptimalG

open Set

noncomputable def rankPotential (phi : ℝ → ℝ) (lam x z : ℝ) : ℝ :=
  if z ≤ lam then 0 else lam - z - ((lam - x) / phi x) * phi z

theorem potential_ratio_ge_one (phi : ℝ → ℝ) (lam x : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x) :
    1 ≤ (lam - x) / phi x := by
  apply (le_div_iff₀ hpos).mpr
  simpa using hcap

theorem rankPotential_low (phi : ℝ → ℝ) (lam x z : ℝ) (hz : z ≤ lam) :
    rankPotential phi lam x z = 0 := by simp [rankPotential, hz]

theorem rankPotential_high_mono (phi : ℝ → ℝ) (lam x y z : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hy : lam < y) (hyz : y ≤ z) (hfall : phi z - phi y ≤ y - z) :
    rankPotential phi lam x y ≤ rankPotential phi lam x z := by
  have hratio := potential_ratio_ge_one phi lam x hpos hcap
  have hz : lam < z := lt_of_lt_of_le hy hyz
  simp only [rankPotential, if_neg (not_le.mpr hy), if_neg (not_le.mpr hz)]
  have h1 := mul_nonneg (sub_nonneg.mpr hratio) (sub_nonneg.mpr hyz)
  have h2 := mul_nonneg (by linarith : 0 ≤ (lam - x) / phi x)
    (by linarith : 0 ≤ phi y - phi z - (z - y))
  nlinarith

theorem rankPotential_nonneg (phi : ℝ → ℝ) (lam x z : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hfall : lam < z → phi z ≤ lam - z) :
    0 ≤ rankPotential phi lam x z := by
  by_cases hz : z ≤ lam
  · simp [rankPotential, hz]
  · have hz' : lam < z := lt_of_not_ge hz
    have hf := hfall hz'
    have hratio := potential_ratio_ge_one phi lam x hpos hcap
    have h1 := mul_nonneg (sub_nonneg.mpr hratio) (by linarith : 0 ≤ z - lam)
    have h2 := mul_nonneg (by linarith : 0 ≤ (lam - x) / phi x)
      (by linarith : 0 ≤ lam - z - phi z)
    simp only [rankPotential, if_neg hz]
    nlinarith

/-- Integrated high-rank slope bounds imply the required monotonicity on [0,1]. -/
theorem rankPotential_monotoneOn (phi : ℝ → ℝ) (lam x : ℝ)
    (hpos : 0 < phi x) (hcap : phi x ≤ lam - x)
    (hzero : phi lam = 0)
    (hfall : ∀ y z, lam ≤ y → y ≤ z → z ≤ 1 → phi z - phi y ≤ y - z) :
    MonotoneOn (rankPotential phi lam x) (Icc 0 1) := by
  intro y hy z hz hyz
  by_cases hyl : y ≤ lam
  · rw [rankPotential_low phi lam x y hyl]
    apply rankPotential_nonneg phi lam x z hpos hcap
    intro hzl
    have hf := hfall lam z le_rfl (le_of_lt hzl) hz.2
    simpa [hzero] using hf
  · exact rankPotential_high_mono phi lam x y z hpos hcap
      (lt_of_not_ge hyl) hyz (hfall y z (le_of_not_ge hyl) hyz hz.2)

/-- The mass-one identity stated after (5.7), including z=λ. -/
theorem rankPotential_mass_one (phi : ℝ → ℝ) (lam x z : ℝ)
    (hpos : 0 < phi x) (hzero : phi lam = 0) (hz : lam ≤ z) :
    phi x * (z + rankPotential phi lam x z - lam) =
      (-phi z) * (lam - x) := by
  by_cases hzl : z ≤ lam
  · have heq : z = lam := le_antisymm hzl hz
    subst z
    simp [rankPotential, hzero]
  · simp only [rankPotential, if_neg hzl]
    field_simp
    ring

end OptimalG
