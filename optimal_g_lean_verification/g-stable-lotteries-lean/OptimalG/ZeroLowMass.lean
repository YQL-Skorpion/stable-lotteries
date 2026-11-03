import OptimalG.VerifierConditions
import OptimalG.Offsets

/-! The degenerate low-score case in Appendix C.1. -/
namespace OptimalG
open Set
open scoped BigOperators

theorem lowScoreMass_nonneg {V : Type*} [Fintype V]
    (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1) :
    0 ≤ lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) := by
  apply Finset.sum_nonneg
  intro v _
  apply mul_nonneg (hw v)
  change 0 ≤ (if s v < lam then phi (s v) else 0)
  split_ifs with hl
  · exact (h.positive ⟨(hs v).1, hl⟩).le
  · rfl

/-- With positive voter weights, zero positive-score mass forces every reference rank to λ. -/
theorem all_ranks_equal_of_zero_lowScoreMass {V : Type*} [Fintype V]
    (w s : V → ℝ) {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hw : ∀ v, 0 < w v) (hs : ∀ v, s v ∈ Icc (0 : ℝ) 1)
    (hmean : 0 ≤ expectation w (fun v => phi (s v)))
    (hA : lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) = 0) :
    ∀ v, s v = lam := by
  classical
  have hterm (v : V) : 0 ≤ w v * (if s v < lam then phi (s v) else 0) := by
    apply mul_nonneg (hw v).le
    split_ifs with hl
    · exact (h.positive ⟨(hs v).1, hl⟩).le
    · rfl
  have hge (v : V) : lam ≤ s v := by
    by_contra hh
    have hl : s v < lam := lt_of_not_ge hh
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i) (Finset.mem_univ v)
    change w v * (if s v < lam then phi (s v) else 0) ≤
      lowExpectation w (fun v => s v < lam) (fun v => phi (s v)) at hle
    rw [hA, if_pos hl] at hle
    exact (not_le_of_gt (mul_pos (hw v) (h.positive ⟨(hs v).1, hl⟩))) hle
  have hnonpos (v : V) : phi (s v) ≤ 0 := h.nonpositive ⟨hge v, (hs v).2⟩
  intro v
  have hsum : expectation w (fun i => phi (s i)) ≤ w v * phi (s v) := by
    calc
      _ ≤ ∑ i, if i = v then w i * phi (s i) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = v
        · simp [hi]
        · simp only [if_neg hi]
          exact mul_nonpos_of_nonneg_of_nonpos (hw i).le (hnonpos i)
      _ = w v * phi (s v) := by simp
  have hp : 0 ≤ phi (s v) := (nonneg_of_mul_nonneg_right (hmean.trans hsum) (hw v))
  apply le_antisymm _ (hge v)
  by_contra hh
  have hl : lam < s v := lt_of_not_ge hh
  have hneg := h.decreasing h.lam_mem (hs v) hl
  rw [h.at_lam] at hneg
  linarith

/-- When all reference ranks are λ, the high inequalities at x=0 suffice and W=0. -/
theorem zeroLow_offset_first {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    {p q k : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hql : q ≤ lam) (hk : k ≤ packingDelta phi p q) : q + beta p * k ≤ lam := by
  have hx : (0 : ℝ) ∈ Ico (0 : ℝ) lam := ⟨le_rfl, h.lam_pos⟩
  have hh := hv.high_first p hp 0 hx q hq hqp
  rw [rankPotential_low phi lam 0 q hql,
    max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hq, hql⟩)), zero_mul, add_zero] at hh
  have hb : q + beta p * packingDelta phi p q - lam ≤ 0 :=
    nonpos_of_mul_nonpos_right hh (h.positive hx)
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  linarith

theorem zeroLow_offset_second {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (beta : ℝ → ℝ) (corr : ℝ → ℝ → ℝ)
    (hv : VerifierOn (Icc 0 1) phi lam beta corr)
    {p q z k : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (hq : 0 ≤ q) (hqp : q ≤ p)
    (hpz : p ≤ z) (hzl : z ≤ lam) (hk : k ≤ packingK phi p q z) : q + beta p * k ≤ 0 := by
  have hx : (0 : ℝ) ∈ Ico (0 : ℝ) lam := ⟨le_rfl, h.lam_pos⟩
  have hh := hv.high_second p hp 0 hx q z hq hqp hpz (hzl.trans h.lam_lt_one.le)
  rw [rankPotential_low phi lam 0 q (hqp.trans (hpz.trans hzl)),
    rankPotential_low phi lam 0 z hzl,
    max_eq_right (neg_nonpos.mpr (h.nonnegative ⟨hp.1.trans hpz, hzl⟩)), zero_mul,
    add_zero, sub_zero] at hh
  have hb : q + beta p * packingK phi p q z ≤ 0 := nonpos_of_mul_nonpos_right hh (h.positive hx)
  have hbk := mul_le_mul_of_nonneg_left hk (hv.beta_nonneg p hp)
  linarith

end OptimalG
