import OptimalG.ParameterTransferField

/-! Terminal tests survive the upward parameter shift with an explicit
positive margin. The argument uses the nonnegative old state and does not
require the old terminal numerator to have a prescribed sign. -/
namespace OptimalG.Variational.ParameterTransfer
open Set

theorem primitive_plateau_closed {lam : ℝ} {d : LowRankData} (h : Admissible lam d)
    {r : ℝ} (hr : tEnd ≤ r) : primitive lam d r=quadratic lam r-d.S := by
  rcases hr.eq_or_lt with he|he
  · subst r
    have hte : ¬tEnd ≤ ell := by norm_num [tEnd,ell]
    simpa only [primitive,if_neg hte,if_pos le_rfl] using h.2.2.2.2.1
  · exact primitive_plateau lam d he

theorem shifted_terminal_difference {lam delta z q : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hz : z ∈ Icc zTest zEnd) (hq : q ∈ Icc qLo qHi) :
    shiftedPrimitive lam d delta (1-z+q)-shiftedPrimitive lam d delta q =
      quadratic lam (1-z+q)-d.S-cap lam d.S q+delta*(1-z+q-0.38) := by
  have hz' : z ∈ Icc (0.84 : ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zTest,zEnd]
  have hq' : q ∈ Icc (0.26 : ℝ) 0.28 := by convert! hq using 1 <;> norm_num [qLo,qHi]
  have hr : 1-z+q ∈ Icc (0.385 : ℝ) 0.44 :=
    ⟨by linarith [hz'.2,hq'.1],by linarith [hz'.1,hq'.2]⟩
  have hrI : 1-z+q ∈ Icc pLo zStart := by
    constructor <;> norm_num [pLo,zStart] <;> linarith [hr.1,hr.2]
  have hqI : q ∈ Icc pLo zStart := by
    constructor <;> norm_num [pLo,zStart] <;> linarith [hq'.1,hq'.2]
  have hqell : q ≤ ell := by norm_num [ell]; linarith [hq'.2]
  dsimp [shiftedPrimitive,shifted]
  rw [clippedPrimitive_eq lam d hrI,clippedPrimitive_eq lam d hqI,
    primitive_plateau_closed h (by norm_num [tEnd]; linarith [hr.1]),
    show primitive lam d q=cap lam d.S q by simp [primitive,hqell],
    gain_after (by linarith [hr.1] : (0.38 : ℝ) ≤ 1-z+q),gain_before (by linarith [hq'.2] : q ≤ 0.38)]
  ring

theorem terminal_obstacle_bound {lam delta z q Y : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hd : 0 ≤ delta)
    (hz : z ∈ Icc zTest zEnd) (hq : q ∈ Icc qLo qHi)
    (hY : 0 ≤ Y) (htest : terminalBound lam d.S z q ≤ Y) :
    z*(shiftedPrimitive lam d delta (1-z+q)-shiftedPrimitive lam d delta q)/(lam+delta-q) ≤
      Y+0.186*delta := by
  have hz' : z ∈ Icc (0.84 : ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zTest,zEnd]
  have hq' : q ∈ Icc (0.26 : ℝ) 0.28 := by convert! hq using 1 <;> norm_num [qLo,qHi]
  have hL := h.compact_lambdaRange
  have hden : 0 < lam-q := by linarith [hL.1,hq'.2]
  have hdenNew : 0 < lam+delta-q := by linarith
  have hold := (div_le_iff₀ hden).mp htest
  have hg : delta*(1-z+q-0.38) ≤ 0.06*delta := by
    have hh := mul_le_mul_of_nonneg_left
      (show 1-z+q-0.38 ≤ (0.06 : ℝ) by linarith [hz'.1,hq'.2]) hd
    nlinarith only [hh]
  have hratio : z ≤ 3.1*(lam+delta-q) := by linarith [hL.1,hq'.2,hz'.2]
  have hprod := mul_le_mul_of_nonneg_right hratio (show 0 ≤ (0.06 : ℝ)*delta by positivity)
  have hgain := mul_le_mul_of_nonneg_left hg (show 0 ≤ z by linarith [hz'.1])
  have hYgain := mul_nonneg hY hd
  rw [shifted_terminal_difference h hz hq]
  apply (div_le_iff₀ hdenNew).mpr
  change z*(quadratic lam (1-z+q)-d.S-cap lam d.S q) ≤ Y*(lam-q) at hold
  nlinarith only [hold,hprod,hgain,hYgain]

theorem root_budget_nonneg {lam z : ℝ} (hL : Certificates.Compact.LambdaRange lam)
    (hz : z ∈ Icc zStart zEnd) : 0 ≤ quadratic lam z-quadratic lam 1 := by
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zStart,zEnd]
  have hh := mul_nonneg (show 0 ≤ 1-z by linarith [hz'.2])
    (show 0 ≤ (1+z)/2-lam by linarith [hz'.1,hL.2])
  unfold quadratic
  nlinarith only [hh]

theorem transferred_terminal_tests {lam delta : ℝ} {d : LowRankData} {Y Z : ℝ → ℝ}
    (h : Admissible lam d) (hd : 0 ≤ delta) (htest : PassesTerminalTests lam d Y)
    (hYlo : ∀ z ∈ Icc zStart zEnd,quadratic lam z-quadratic lam 1 ≤ Y z)
    (hflow : ∀ z ∈ Icc zStart zEnd,Y z+0.26412*delta ≤ Z z) :
    ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(shiftedPrimitive lam d delta (1-z+q)-shiftedPrimitive lam d delta q)/(lam+delta-q)+
        0.07812*delta ≤ Z z := by
  intro z hz q hq
  have hzfull : z ∈ Icc zStart zEnd :=
    ⟨(by norm_num [zStart,zTest] : zStart ≤ zTest).trans hz.1,hz.2⟩
  have hY := (root_budget_nonneg h.compact_lambdaRange hzfull).trans (hYlo z hzfull)
  have hh := terminal_obstacle_bound h hd hz hq hY (htest z hz q hq)
  have hf := hflow z hzfull
  linarith

end OptimalG.Variational.ParameterTransfer
