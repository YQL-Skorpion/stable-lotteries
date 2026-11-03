import OptimalG.ThreeClassAuxiliaryWitness
import OptimalG.AuxiliaryWeightCorrection
import OptimalG.OddGrid

/-! # Real Election 3 tests are witnessed by actual finite equal-voter elections -/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- The finite-to-real bridge for the three classes. The high-class primitive
is positive at p and 1-p; the reference may initially have zero stability margin.
Two small auxiliary types make that margin strict and correct rounding exactly. -/
theorem real_three_class_strict_witness (g : ℝ → ℝ) (hg : Continuous g)
    (lam p x y z : ℝ) (hlam : 0 ≤ lam)
    (hp : p ∈ Ioo 0 1) (hx : 0 ≤ x) (hxp : x < 1 - p)
    (hpy : p ≤ y) (hy1 : y < 1) (hpz : p < z) (hz1 : z ≤ 1)
    (r : ℝ) (hr : r ∈ Icc 0 1) (hrbelow : g r < activationPrimitive g 1)
    (hendpoint : activationPrimitive g 1 < g 1)
    (hR : 0 < centeredPrimitive g p) (hP : 0 < centeredPrimitive g (1 - p))
    (w : Fin 3 → ℝ) (hw : ∀ t, 0 ≤ w t) (hwsum : ∑ t, w t = 1)
    (hbalance : expectation w ![centeredPrimitive g (1 - p),
      centeredPrimitive g (z - p) - centeredPrimitive g z, -centeredPrimitive g p] = 0)
    (hreference : expectation w ![g x, g z, g y] ≤ activationPrimitive g 1)
    (hexcess : 0 < expectation w (fun t => ![x, z, p + y] t - lam * ![2, 1, 1] t)) :
    WitnessAbove g (1 + 2 * lam) := by
  let J := centeredPrimitive g
  let mean := activationPrimitive g 1
  let pn := fun n => oddGrid n p
  let xn := fun n => oddGrid n x
  let yn := fun n => oddGrid n y
  let zn := fun n => oddGrid n z
  let rn := fun n => oddGrid n r
  have hpLim : Tendsto pn atTop (𝓝 p) := oddGrid_tendsto p hp.1.le
  have hxLim : Tendsto xn atTop (𝓝 x) := oddGrid_tendsto x hx
  have hyLim : Tendsto yn atTop (𝓝 y) := oddGrid_tendsto y (hp.1.le.trans hpy)
  have hzLim : Tendsto zn atTop (𝓝 z) := oddGrid_tendsto z (hp.1.le.trans hpz.le)
  have hrLim : Tendsto rn atTop (𝓝 r) := oddGrid_tendsto r hr.1
  have hJ : Continuous J := centeredPrimitive_continuous g hg
  let Rn := fun n => J (pn n)
  let Pn := fun n => J (1 - pn n)
  let En := fun n => expectation w ![J (1 - pn n), J (zn n - pn n) - J (zn n), -J (pn n)]
  let An := fun n => expectation w (fun t => ![g (xn n), g (zn n), g (yn n)] t - mean)
  let Bn := fun n => expectation w (fun t => ![xn n, zn n, pn n + yn n] t - lam * ![2, 1, 1] t)
  let Sn := fun n => g (rn n) - mean
  let A := expectation w (fun t => ![g x, g z, g y] t - mean)
  let B := expectation w (fun t => ![x, z, p + y] t - lam * ![2, 1, 1] t)
  have hA : A ≤ 0 := by
    have he : A = expectation w ![g x, g z, g y] - mean := by
      dsimp [A]
      simp only [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum, one_mul]
    rw [he]
    exact sub_nonpos.mpr hreference
  have hRlim : Tendsto Rn atTop (𝓝 (J p)) := hJ.continuousAt.tendsto.comp hpLim
  have hPlim : Tendsto Pn atTop (𝓝 (J (1 - p))) := hJ.continuousAt.tendsto.comp (tendsto_const_nhds.sub hpLim)
  have hElim : Tendsto En atTop (𝓝 0) := by
    rw [← hbalance]
    apply expectation_tendsto
    exact tendsto_vec3 _ _ _ _ _ _ hPlim
      ((hJ.continuousAt.tendsto.comp (hzLim.sub hpLim)).sub (hJ.continuousAt.tendsto.comp hzLim)) hRlim.neg
  have hAlim : Tendsto An atTop (𝓝 A) := by
    apply expectation_tendsto
    intro t
    exact (tendsto_vec3 _ _ _ _ _ _ (hg.continuousAt.tendsto.comp hxLim)
      (hg.continuousAt.tendsto.comp hzLim) (hg.continuousAt.tendsto.comp hyLim) t).sub tendsto_const_nhds
  have hBlim : Tendsto Bn atTop (𝓝 B) := by
    apply expectation_tendsto
    intro t
    exact (tendsto_vec3 _ _ _ _ _ _ hxLim hzLim (hpLim.add hyLim) t).sub tendsto_const_nhds
  have hSlim : Tendsto Sn atTop (𝓝 (g r - mean)) :=
    (hg.continuousAt.tendsto.comp hrLim).sub tendsto_const_nhds
  obtain ⟨eps, heps, hcorrect⟩ := exists_eventually_positive_auxiliary_correction lam (J p) (J (1 - p)) A B
    (g r - mean) hlam hR hP hA hexcess (sub_neg.mpr hrbelow) Rn Pn En An Bn Sn
    hRlim hPlim hElim hAlim hBlim hSlim
  have hcyc := eventually_odd_grid_difference g hg.continuousOn r 1 hr (by norm_num)
    (ne_of_lt (hrbelow.trans hendpoint))
  have hxp' : x + p < 1 := by linarith
  have hall : ∀ᶠ n in atTop,
      0 < pn n ∧ pn n < 1 ∧ xn n + pn n < 1 ∧ yn n < 1 ∧ pn n < zn n ∧
      (let u := eps * Rn n - En n / (Pn n + Rn n)
       let v := eps * Pn n + En n / (Pn n + Rn n)
       0 < u ∧ 0 < v ∧ En n + u * Pn n - v * Rn n = 0 ∧
         An n + (u + v) * Sn n < 0 ∧ 0 < Bn n - 2 * lam * (u + v)) ∧
      ∃ j ≤ 2 * n, g (((j + 2 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) ≠
        g (((j + 1 : ℕ) : ℝ) / (2 * n + 3 : ℕ)) := by
    filter_upwards [hpLim.eventually_const_lt hp.1, hpLim.eventually_lt_const hp.2,
      (hxLim.add hpLim).eventually_lt_const hxp', hyLim.eventually_lt_const hy1,
      (hpLim.sub hzLim).eventually_lt_const (sub_neg.mpr hpz), hcorrect, hcyc]
      with n hn0 hn1 hnx hny hnz hnc hng
    exact ⟨hn0, hn1, hnx, hny, sub_neg.mp hnz, hnc, hng⟩
  obtain ⟨n, hn0, hn1, hnx, hny, hnz, hnc, j0, hj0, hjdiff⟩ := hall.exists
  let m := 2 * n + 3
  let h := oddGridIndex n p
  let low := m - h
  let ix := oddGridIndex n x
  let iy := oddGridIndex n y
  let iz := oddGridIndex n z
  let ir := oddGridIndex n r
  have hmpos : (0 : ℝ) < m := by dsimp [m]; positivity
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hpval : pn n = (h : ℝ) / m := rfl
  have hxval : xn n = (ix : ℝ) / m := rfl
  have hyval : yn n = (iy : ℝ) / m := rfl
  have hzval : zn n = (iz : ℝ) / m := rfl
  have hrval : rn n = (ir : ℝ) / m := rfl
  have hh : 0 < h := by
    rw [hpval] at hn0
    have hz : (0 : ℝ) / m < (h : ℝ) / m := by simpa using hn0
    exact_mod_cast (div_lt_div_iff_of_pos_right hmpos).mp hz
  have hhm : h < m := by rw [hpval] at hn1; exact_mod_cast (div_lt_one hmpos).mp hn1
  have hlow : 0 < low := by dsimp [low]; omega
  have hsum : low + h = m := by dsimp [low]; omega
  have hix : ix ≤ low := by
    rw [hxval, hpval, ← add_div] at hnx
    have hn := (div_lt_one hmpos).mp hnx
    have hn' : ix + h < m := by exact_mod_cast hn
    omega
  have hiyh : h ≤ iy := oddGridIndex_mono n hpy
  have hiym : iy < low + h := by
    rw [hyval] at hny
    have hn : iy < m := by exact_mod_cast (div_lt_one hmpos).mp hny
    omega
  have hizh : h < iz := by
    rw [hpval, hzval] at hnz
    exact_mod_cast (div_lt_div_iff_of_pos_right hmpos).mp hnz
  have hizm : iz ≤ low + h := by rw [hsum]; exact oddGridIndex_le n z hz1
  have hirm : ir ≤ low + h := by rw [hsum]; exact oddGridIndex_le n r hr.2
  letI : NeZero (low + h) := ⟨by omega⟩
  let a : Fin (low + h) := ⟨j0, by dsimp [m] at hsum; omega⟩
  let b : Fin (low + h) := ⟨j0 + 1, by dsimp [m] at hsum; omega⟩
  let c : Fin (low + h) := ⟨j0 + 2, by dsimp [m] at hsum; omega⟩
  have hstrength : cyclicStrength g a (1 / (low + h : ℕ)) ≠ 0 := by
    rw [cyclicStrength_uniform_grid]
    apply div_ne_zero _ (mul_ne_zero (by norm_num) (one_div_ne_zero (by positivity)))
    apply sub_ne_zero.mpr
    simpa only [a, hsum] using hjdiff
  let e : PairedSupport (n + 1) ≃ Fin (low + h) := Fintype.equivOfCardEq (by
    simp only [PairedSupport, Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    dsimp [m] at hsum
    omega)
  have hlowval : (low : ℝ) / (low + h : ℕ) = 1 - pn n := by
    rw [hpval, hsum]
    have hsR : (low : ℝ) + h = m := by exact_mod_cast hsum
    field_simp
    linarith
  have hdiffval : ((iz - h : ℕ) : ℝ) / (low + h : ℕ) = zn n - pn n := by
    rw [hpval, hzval, hsum, Nat.cast_sub hizh.le, sub_div]
  have hvals : (h : ℝ) / (low + h : ℕ) = pn n ∧ (ix : ℝ) / (low + h : ℕ) = xn n ∧
      (iy : ℝ) / (low + h : ℕ) = yn n ∧ (iz : ℝ) / (low + h : ℕ) = zn n ∧
      (ir : ℝ) / (low + h : ℕ) = rn n := by rw [hsum]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hcostval : ((h : ℝ) + iy) / (low + h : ℕ) = pn n + yn n := by rw [add_div, hvals.1, hvals.2.2.1]
  rcases hnc with ⟨hnu, hnv, hnbal, hnref, hncost⟩
  apply three_class_auxiliary_grid_witness g hg lam hlam low h ix iy iz ir (n + 1)
    hlow hh hix hiyh hiym hizh hizm hirm e a b c rfl rfl hstrength w hw hwsum _ _ hnu.le hnv.le
  · simpa only [hlowval, hdiffval, hvals.1, hvals.2.2.2.1] using hnbal
  · simpa only [hvals.2.1, hvals.2.2.1, hvals.2.2.2.1, hvals.2.2.2.2] using hnref
  · simpa only [hvals.2.1, hvals.2.2.2.1, hcostval] using hncost

end OptimalG
