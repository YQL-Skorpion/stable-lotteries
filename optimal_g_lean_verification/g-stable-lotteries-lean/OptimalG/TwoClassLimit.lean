import OptimalG.TwoClassWitness
import OptimalG.Normalization

/-! # The real two-class inequality from actual finite equal-voter elections -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem centeredPrimitive_continuous (g : ℝ → ℝ) (hg : Continuous g) :
    Continuous (centeredPrimitive g) :=
  (continuous_id.mul continuous_const).sub
    (intervalIntegral.differentiable_integral_of_continuous hg).continuous

theorem centeredPrimitive_zero (g : ℝ → ℝ) : centeredPrimitive g 0 = 0 := by
  simp [centeredPrimitive, activationPrimitive]

theorem centeredPrimitive_one (g : ℝ → ℝ) : centeredPrimitive g 1 = 0 := by
  simp [centeredPrimitive]

/-- Strict two-class violations survive simultaneous finite candidate-grid
approximation and the exact equal-voter realization theorem. -/
theorem real_two_class_strict_witness (g : ℝ → ℝ) (hg : Continuous g)
    (lam p q : ℝ) (hlam : 0 ≤ lam) (hp : p ∈ Ioo 0 1) (hq : 0 ≤ q) (hqp : q < p)
    (r s : ℝ) (hr : r ∈ Icc 0 1) (hs : s ∈ Icc 0 1) (hne : g r ≠ g s)
    (hR : 0 < centeredPrimitive g p)
    (hdelta : 0 < centeredPrimitive g (1 - p + q) - centeredPrimitive g q)
    (hexcess : (lam - q) * centeredPrimitive g p <
      p * (centeredPrimitive g (1 - p + q) - centeredPrimitive g q)) :
    WitnessAbove g (1 + 2 * lam) := by
  let P := fun n : ℕ => lowerGrid (2 * n + 2) p
  let Q := fun n : ℕ => lowerGrid (2 * n + 2) q
  have ht : Tendsto (fun n : ℕ => 2 * n + 2) atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have ht2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 (fun k => ?_)
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hP : Tendsto P atTop (𝓝 p) := (lowerGrid_tendsto p hp.1.le).comp ht
  have hQ : Tendsto Q atTop (𝓝 q) := (lowerGrid_tendsto q hq).comp ht
  have hJ := centeredPrimitive_continuous g hg
  have hRP := hJ.continuousAt.tendsto.comp hP
  have hDQ : Tendsto (fun n => centeredPrimitive g (1 - P n + Q n) - centeredPrimitive g (Q n))
      atTop (𝓝 (centeredPrimitive g (1 - p + q) - centeredPrimitive g q)) :=
    (hJ.continuousAt.tendsto.comp ((tendsto_const_nhds.sub hP).add hQ)).sub
      (hJ.continuousAt.tendsto.comp hQ)
  have hE := (((tendsto_const_nhds.sub hQ).mul hRP).sub (hP.mul hDQ)).eventually_lt_const
    (sub_neg.mpr hexcess)
  have hcyc := (eventually_exists_interior_grid_difference g hg.continuousOn r s hr hs hne).filter_mono ht2
  have hall : ∀ᶠ n in atTop, 0 < P n ∧ P n < 1 ∧ Q n < P n ∧
      0 < centeredPrimitive g (P n) ∧
      0 < centeredPrimitive g (1 - P n + Q n) - centeredPrimitive g (Q n) ∧
      (lam - Q n) * centeredPrimitive g (P n) <
        P n * (centeredPrimitive g (1 - P n + Q n) - centeredPrimitive g (Q n)) ∧
      ∃ j ≤ 2 * n, g (((j + 2 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) ≠
        g (((j + 1 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) := by
    filter_upwards [hP.eventually_const_lt hp.1, hP.eventually_lt_const hp.2,
      (hQ.sub hP).eventually_lt_const (sub_neg.mpr hqp), hRP.eventually_const_lt hR,
      hDQ.eventually_const_lt hdelta, hE, hcyc] with n hn0 hn1 hnqp hnR hnD hnE hnC
    exact ⟨hn0, hn1, sub_neg.mp hnqp, hnR, hnD, sub_neg.mp hnE, hnC⟩
  obtain ⟨n, hn0, hn1, hnqp, hnR, hnD, hnE, j, hj, hjdiff⟩ := hall.exists
  let m := 2 * n + 3
  let h := ⌊(m : ℝ) * p⌋₊
  let k := ⌊(m : ℝ) * q⌋₊
  let z := m - h
  have hmpos : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hPval : P n = (h : ℝ) / m := by rfl
  have hQval : Q n = (k : ℝ) / m := by rfl
  have hh : 0 < h := by
    rw [hPval] at hn0
    have hzero : (0 : ℝ) / m < (h : ℝ) / m := by simpa using hn0
    exact_mod_cast (div_lt_div_iff_of_pos_right hmR).mp hzero
  have hhm : h < m := by
    rw [hPval] at hn1
    exact_mod_cast (div_lt_one hmR).mp hn1
  have hkh : k < h := by
    rw [hPval, hQval] at hnqp
    exact_mod_cast (div_lt_div_iff_of_pos_right hmR).mp hnqp
  have hz : 0 < z := by dsimp [z]; omega
  have hsum : h + z = m := by dsimp [z]; omega
  letI : NeZero (h + z) := ⟨by omega⟩
  let a : Fin (h + z) := ⟨j, by dsimp [m] at hsum; omega⟩
  let b : Fin (h + z) := ⟨j + 1, by dsimp [m] at hsum; omega⟩
  let c : Fin (h + z) := ⟨j + 2, by dsimp [m] at hsum; omega⟩
  have hstrength : cyclicStrength g a (1 / (h + z : ℕ)) ≠ 0 := by
    rw [cyclicStrength_uniform_grid]
    apply div_ne_zero _ (mul_ne_zero (by norm_num) (one_div_ne_zero (by positivity)))
    apply sub_ne_zero.mpr
    simpa only [a, hsum] using hjdiff
  let e : PairedSupport (n + 1) ≃ Fin (h + z) := Fintype.equivOfCardEq (by
    simp only [PairedSupport, Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    dsimp [m] at hsum
    omega)
  have hend : ((k + z : ℕ) : ℝ) / (h + z : ℕ) = 1 - P n + Q n := by
    rw [hPval, hQval, hsum]
    have hzR : (h : ℝ) + z = m := by exact_mod_cast hsum
    push_cast
    field_simp
    linarith
  have hpval : (h : ℝ) / (h + z : ℕ) = P n := by rw [hsum, hPval]
  have hqval : (k : ℝ) / (h + z : ℕ) = Q n := by rw [hsum, hQval]
  apply two_class_grid_strict_witness g hg lam hlam h z k (n + 1) hh hz hkh e a b c rfl rfl hstrength
  · simpa only [hpval] using hnR
  · simpa only [hend, hqval] using hnD
  · simpa only [hpval, hqval, hend] using hnE

/-- The two-class inequality is necessary for actual finite equal-voter
universal distortion bounds, wherever its primitive is positive. -/
theorem real_two_class_necessary (g : ℝ → ℝ) (hg : Continuous g)
    (lam : ℝ) (hlam : 0 ≤ lam) (hbound : UniversalBound g (1 + 2 * lam))
    (p q : ℝ) (hp : p ∈ Ioo 0 1) (hq : 0 ≤ q) (hqp : q ≤ p) (hqlam : q ≤ lam)
    (hR : 0 < centeredPrimitive g p) :
    p * (centeredPrimitive g (1 - p + q) - centeredPrimitive g q) ≤
      (lam - q) * centeredPrimitive g p := by
  by_cases heq : q = p
  · subst q
    rw [show 1 - p + p = 1 by ring, centeredPrimitive_one, zero_sub]
    nlinarith [mul_nonneg (sub_nonneg.mpr hqlam) hR.le, mul_pos hp.1 hR]
  by_contra! hviolation
  have hdelta : 0 < centeredPrimitive g (1 - p + q) - centeredPrimitive g q := by
    have hright : 0 ≤ (lam - q) * centeredPrimitive g p := mul_nonneg (sub_nonneg.mpr hqlam) hR.le
    by_contra! hd
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hp.1.le hd
    linarith
  have hend := endpoint_above_mean_of_universalBound g lam hlam hbound
  obtain ⟨s, hs, hsbelow⟩ := exists_rank_below_mean g hg.continuousOn hend
  have hne : g s ≠ g 1 := ne_of_lt (hsbelow.trans hend)
  exact witnessAbove_not_universalBound g _ (real_two_class_strict_witness g hg lam p q hlam hp hq
    (lt_of_le_of_ne hqp heq) s 1 hs (by norm_num) hne hR hdelta hviolation) hbound

end OptimalG
