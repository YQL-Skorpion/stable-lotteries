import OptimalG.Algebra
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-! Existence of the balanced supporting coefficients in Section 5.2. -/
namespace OptimalG
open Set

noncomputable def supportMaximum (phi : ℝ → ℝ) (K : Set ℝ) (eta : ℝ) : ℝ :=
  sSup ((fun x => x + eta * phi x) '' K)

theorem supportMaximum_attained (phi : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hc : ContinuousOn phi K) (eta : ℝ) :
    ∃ x ∈ K, supportMaximum phi K eta = x + eta * phi x ∧
      ∀ y ∈ K, y + eta * phi y ≤ x + eta * phi x :=
  hK.exists_sSup_image_eq_and_ge hne (continuousOn_id.add (hc.const_mul eta))

theorem le_supportMaximum (phi : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hc : ContinuousOn phi K) (eta x : ℝ) (hx : x ∈ K) :
    x + eta * phi x ≤ supportMaximum phi K eta := by
  obtain ⟨y, hy, heq, hmax⟩ := supportMaximum_attained phi K hK hne hc eta
  rw [heq]
  exact hmax x hx

theorem supportMaximum_continuous (phi : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hc : ContinuousOn phi K) : Continuous (supportMaximum phi K) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hf : Continuous (fun p : ℝ × K => (p.2 : ℝ) + p.1 * phi p.2) :=
    (continuous_subtype_val.comp continuous_snd).add
      (continuous_fst.mul (hc.restrict.comp continuous_snd))
  have hh := (isCompact_univ : IsCompact (Set.univ : Set K)).continuous_sSup (f :=
    fun eta (x : K) => (x : ℝ) + eta * phi x) hf
  have heq (eta : ℝ) : ((fun x : K => (x : ℝ) + eta * phi x) '' Set.univ) =
      ((fun x : ℝ => x + eta * phi x) '' K) := by
    ext u
    simp
  change Continuous (fun eta => sSup ((fun x => x + eta * phi x) '' K))
  simpa only [heq] using hh

theorem supportMaximum_strictMono (phi : ℝ → ℝ) (K : Set ℝ)
    (hK : IsCompact K) (hne : K.Nonempty) (hc : ContinuousOn phi K)
    (hp : ∀ x ∈ K, 0 < phi x) : StrictMono (supportMaximum phi K) := by
  intro a b hab
  obtain ⟨x, hx, heq, _⟩ := supportMaximum_attained phi K hK hne hc a
  have hle := le_supportMaximum phi K hK hne hc b x hx
  have hlt := mul_lt_mul_of_pos_right hab (hp x hx)
  rw [heq]
  linarith

/-- The balance equation has exactly one positive solution whenever its target
lies above the value at zero. -/
theorem supporting_balance_exists_unique (phi : ℝ → ℝ) (K L : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) (hneK : K.Nonempty) (hneL : L.Nonempty)
    (hcK : ContinuousOn phi K) (hcL : ContinuousOn phi L)
    (hpK : ∀ x ∈ K, 0 < phi x) (hpL : ∀ y ∈ L, 0 < phi y)
    (R P T : ℝ) (hR : 0 < R) (hP : 0 < P)
    (hzero : R * supportMaximum phi K 0 + P * supportMaximum phi L 0 < T) :
    ∃! eta : ℝ, 0 < eta ∧ R * supportMaximum phi K eta + P * supportMaximum phi L eta = T := by
  let F := fun eta => R * supportMaximum phi K eta + P * supportMaximum phi L eta
  have hcont : Continuous F := (supportMaximum_continuous phi K hK hcK).const_mul R |>.add
    ((supportMaximum_continuous phi L hL hcL).const_mul P)
  have hmono : StrictMono F := by
    intro a b hab
    exact add_lt_add (mul_lt_mul_of_pos_left (supportMaximum_strictMono phi K hK hneK hcK hpK hab) hR)
      (mul_lt_mul_of_pos_left (supportMaximum_strictMono phi L hL hneL hcL hpL hab) hP)
  obtain ⟨x, hx⟩ := hneK
  obtain ⟨y, hy⟩ := hneL
  let slope := R * phi x + P * phi y
  have hslope : 0 < slope := add_pos (mul_pos hR (hpK x hx)) (mul_pos hP (hpL y hy))
  let B := max 1 ((T - (R * x + P * y)) / slope + 1)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hB := le_max_right (1 : ℝ) ((T - (R * x + P * y)) / slope + 1)
  have hBmul := mul_le_mul_of_nonneg_right hB hslope.le
  rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hslope), one_mul] at hBmul
  have hBx := mul_le_mul_of_nonneg_left (le_supportMaximum phi K hK ⟨x, hx⟩ hcK B x hx) hR.le
  have hBy := mul_le_mul_of_nonneg_left (le_supportMaximum phi L hL ⟨y, hy⟩ hcL B y hy) hP.le
  have hFB : T ≤ F B := by dsimp [F, slope] at *; nlinarith
  obtain ⟨eta, heta, heq⟩ := intermediate_value_Icc hBpos.le hcont.continuousOn
    (show T ∈ Icc (F 0) (F B) from ⟨hzero.le, hFB⟩)
  have hpos : 0 < eta := by
    rcases eq_or_lt_of_le heta.1 with hh | hh
    · rw [← hh] at heq
      exact False.elim (ne_of_lt hzero heq)
    · exact hh
  refine ⟨eta, ⟨hpos, heq⟩, ?_⟩
  intro eta' hh
  apply hmono.injective
  exact hh.2.trans heq.symm

/-- Balanced support lines with actual maximizing ranks and positive coefficients.
The determinant gap is the strict inequality at eta=0. -/
theorem supporting_coefficients_exist (phi : ℝ → ℝ) (K L : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) (hneK : K.Nonempty) (hneL : L.Nonempty)
    (hcK : ContinuousOn phi K) (hcL : ContinuousOn phi L)
    (hpK : ∀ x ∈ K, 0 < phi x) (hpL : ∀ y ∈ L, 0 < phi y)
    (lam p R P : ℝ) (hR : 0 < R) (hP : 0 < P)
    (hdet : ∀ x ∈ K, ∀ y ∈ L, 0 < determinant lam p x y R P)
    (hyhigh : ∃ y ∈ L, lam - p ≤ y) :
    ∃ eta beta x y : ℝ, 0 < eta ∧ 0 < beta ∧ x ∈ K ∧ y ∈ L ∧
      eta * phi x = 2 * lam - x - beta * P ∧
      eta * phi y = lam - p - y + beta * R ∧
      (∀ t ∈ K, t + eta * phi t ≤ 2 * lam - beta * P) ∧
      (∀ t ∈ L, t + eta * phi t ≤ lam - p + beta * R) := by
  have hzero : R * supportMaximum phi K 0 + P * supportMaximum phi L 0 <
      2 * lam * R + (lam - p) * P := by
    obtain ⟨x, hx, heqx, _⟩ := supportMaximum_attained phi K hK hneK hcK 0
    obtain ⟨y, hy, heqy, _⟩ := supportMaximum_attained phi L hL hneL hcL 0
    rw [heqx, heqy]
    have hh := hdet x hx y hy
    unfold determinant at hh
    nlinarith
  obtain ⟨eta, ⟨heta, hbalance⟩, _⟩ := supporting_balance_exists_unique phi K L hK hL hneK hneL
    hcK hcL hpK hpL R P (2 * lam * R + (lam - p) * P) hR hP hzero
  obtain ⟨x, hx, heqx, hmaxx⟩ := supportMaximum_attained phi K hK hneK hcK eta
  obtain ⟨y, hy, heqy, hmaxy⟩ := supportMaximum_attained phi L hL hneL hcL eta
  rw [heqx, heqy] at hbalance
  let beta := (y + eta * phi y + p - lam) / R
  have hbetaR : beta * R = y + eta * phi y + p - lam := div_mul_cancel₀ _ (ne_of_gt hR)
  have hbeta : 0 < beta := by
    obtain ⟨t, ht, htlo⟩ := hyhigh
    have hm := hmaxy t ht
    have hp := mul_pos heta (hpL t ht)
    apply div_pos _ hR
    linarith
  have hyid : eta * phi y = lam - p - y + beta * R := by linarith
  have hxid : eta * phi x = 2 * lam - x - beta * P := by
    have heq : R * (eta * phi x - (2 * lam - x - beta * P)) = 0 := by nlinarith
    have hh := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hR)
    linarith
  refine ⟨eta, beta, x, y, heta, hbeta, hx, hy, hxid, hyid, ?_, ?_⟩
  · intro t ht; have hh := hmaxx t ht; linarith
  · intro t ht; have hh := hmaxy t ht; linarith

end OptimalG
