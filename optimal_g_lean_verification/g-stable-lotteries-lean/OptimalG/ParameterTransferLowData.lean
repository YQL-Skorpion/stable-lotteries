import OptimalG.ParameterTransferField

/-! Low-rank constraints of the actual transferred competitor. -/
namespace OptimalG.Variational.ParameterTransfer
open Set MeasureTheory

theorem cap_low_monotone {lam : ℝ} {d : LowRankData} (h : Admissible lam d) :
    MonotoneOn (cap lam d.S) (Icc pLo tEnd) := by
  intro a ha b hb hab
  have ha1 : a ≤ (0.385 : ℝ) := by convert! ha.2 using 1 <;> norm_num [tEnd]
  have hb1 : b ≤ (0.385 : ℝ) := by convert! hb.2 using 1 <;> norm_num [tEnd]
  have hprod := mul_le_mul (show (0.615 : ℝ) ≤ 1-a by linarith)
    (show (0.615 : ℝ) ≤ 1-b by linarith) (by norm_num : (0 : ℝ) ≤ 0.615)
    (show 0 ≤ 1-a by linarith)
  have hden : 0 < (1-a)*(1-b) := by nlinarith only [hprod]
  have hL := h.compact_lambdaRange
  have hgap : 0 ≤ (1-a)*(1-b)/2-d.S := by linarith [h.slack_upper]
  have hscaled := mul_nonneg (show 0 ≤ lam by linarith [hL.1]) hgap
  have hfrac : lam*d.S/((1-a)*(1-b)) ≤ lam/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hscaled]
  have hgain := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hfrac)
  rw [← cap_difference lam d.S a b (by linarith) (by linarith)] at hgain
  linarith

theorem primitive_low_cap {lam : ℝ} {d : LowRankData} (h : Admissible lam d)
    {r : ℝ} (hr : r ∈ Icc pLo tEnd) : primitive lam d r ≤ cap lam d.S r := by
  unfold primitive
  split_ifs with he ht
  · exact le_rfl
  · exact h.lowPrimitive_le_cap ⟨le_of_not_ge he,hr.2⟩
  · exact (ht hr.2).elim

theorem primitive_eq_lowPrimitive {lam r : ℝ} {d : LowRankData} (hr : r ∈ Icc ell tEnd) :
    primitive lam d r=lowPrimitive lam d r := by
  by_cases he : r ≤ ell
  · have hh : r=ell := le_antisymm he hr.1
    subst r
    rw [primitive_at_ell,lowPrimitive_at_ell]
  · simp only [primitive,if_neg he,if_pos hr.2]

theorem primitive_low_monotone {lam : ℝ} {d : LowRankData} (h : Admissible lam d) :
    MonotoneOn (primitive lam d) (Icc pLo tEnd) := by
  intro a ha b hb hab
  by_cases hbe : b ≤ ell
  · have hae := hab.trans hbe
    simp only [primitive,if_pos hae,if_pos hbe]
    exact cap_low_monotone h ha hb hab
  · by_cases hae : a ≤ ell
    · rw [show primitive lam d a=cap lam d.S a by simp only [primitive,if_pos hae],
        primitive_eq_lowPrimitive ⟨le_of_not_ge hbe,hb.2⟩]
      have hcap := cap_low_monotone h ha (show ell ∈ Icc pLo tEnd by norm_num [ell,pLo,tEnd]) hae
      have hlow := h.lowPrimitive_monotone.1 (show ell ∈ Icc ell tEnd by norm_num [ell,tEnd])
        ⟨le_of_not_ge hbe,hb.2⟩ (le_of_not_ge hbe)
      rw [lowPrimitive_at_ell] at hlow
      exact hcap.trans hlow
    · rw [primitive_eq_lowPrimitive ⟨le_of_not_ge hae,ha.2⟩,
        primitive_eq_lowPrimitive ⟨le_of_not_ge hbe,hb.2⟩]
      exact h.lowPrimitive_monotone.1 ⟨le_of_not_ge hae,ha.2⟩ ⟨le_of_not_ge hbe,hb.2⟩ hab

theorem shiftedPrimitive_eq (lam delta : ℝ) (d : LowRankData) {r : ℝ}
    (hr : r ∈ Icc pLo zStart) :
    shiftedPrimitive lam d delta r=shifted (primitive lam d) delta r := by
  simp only [shiftedPrimitive,shifted,clippedPrimitive_eq lam d hr]

theorem shifted_low_monotone {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hd : 0 ≤ delta) :
    MonotoneOn (shiftedPrimitive lam d delta) (Icc pLo tEnd) := by
  intro a ha b hb hab
  rw [shiftedPrimitive_eq lam delta d ⟨ha.1,ha.2.trans (by norm_num [tEnd,zStart])⟩,
    shiftedPrimitive_eq lam delta d ⟨hb.1,hb.2.trans (by norm_num [tEnd,zStart])⟩]
  exact shifted_monotoneOn (primitive_low_monotone h) hd ha hb hab

theorem shifted_root_bound {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hd : 0 ≤ delta) {r : ℝ} (hr : r ∈ Icc pLo zStart) :
    quadratic (lam+delta) r-scalar d.S delta ≤ shiftedPrimitive lam d delta r := by
  rw [shiftedPrimitive_eq lam delta d hr]
  exact shifted_root hd (h.primitive_lower hr)

theorem shifted_cap_bound {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hd : 0 ≤ delta) {r : ℝ} (hr : r ∈ Icc pLo tEnd) :
    shiftedPrimitive lam d delta r ≤ cap (lam+delta) (scalar d.S delta) r := by
  rw [shiftedPrimitive_eq lam delta d ⟨hr.1,hr.2.trans (by norm_num [tEnd,zStart])⟩]
  apply shifted_cap h.compact_lambdaRange (by convert! h.slack_upper using 1 <;> norm_num) hd
    (by convert! hr using 1 <;> norm_num [pLo,tEnd]) (primitive_low_cap h hr)

theorem shifted_scalar_bounds {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta)) (hd : 0 ≤ delta) :
    Certificates.Compact.ScalarRange (scalar d.S delta) := by
  have hlo := h.slack_lower_exact
  have hhi := scalar_slackUpper hd h.2.1
  constructor
  · unfold scalar
    linarith
  · unfold slackUpper at hhi
    norm_num [Certificates.Compact.scalarUpper,lambdaHi] at *
    linarith [hLnew.2]

theorem shifted_low_increment {lam delta a b : ℝ} {d : LowRankData}
    (h : Admissible lam d) (ha : a ∈ Icc ell xHi) (hb : b ∈ Icc ell xHi) :
    shiftedPrimitive lam d delta b-shiftedPrimitive lam d delta a=∫ r in a..b,d.phi r := by
  have haI : a ∈ Icc pLo zStart :=
    ⟨(by norm_num [pLo,ell] : pLo ≤ ell).trans ha.1,ha.2.trans (by norm_num [xHi,zStart])⟩
  have hbI : b ∈ Icc pLo zStart :=
    ⟨(by norm_num [pLo,ell] : pLo ≤ ell).trans hb.1,hb.2.trans (by norm_num [xHi,zStart])⟩
  have hat : a ∈ Icc ell tEnd := ⟨ha.1,ha.2.trans (by norm_num [xHi,tEnd])⟩
  have hbt : b ∈ Icc ell tEnd := ⟨hb.1,hb.2.trans (by norm_num [xHi,tEnd])⟩
  rw [shiftedPrimitive_eq lam delta d hbI,shiftedPrimitive_eq lam delta d haI]
  dsimp [shifted]
  rw [gain_before (by convert! hb.2 using 1 <;> norm_num [xHi]),
    gain_before (by convert! ha.2 using 1 <;> norm_num [xHi]),
    primitive_eq_lowPrimitive hbt,primitive_eq_lowPrimitive hat]
  have hh := h.lowPrimitive_sub hat hbt
  linarith

end OptimalG.Variational.ParameterTransfer
