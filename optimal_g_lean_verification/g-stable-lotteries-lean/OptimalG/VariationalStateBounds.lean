import OptimalG.VariationalContinuation
import OptimalG.VariationalRecovery
import OptimalG.Certificates.VariationalBridge

/-! Feasible continuations stay in the certified state rectangle, and every
sufficiently near-active control has positive state coefficient. -/
namespace OptimalG.Variational
open Set MeasureTheory

 theorem continuation_defect_monotone {lam : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hY : IsContinuation lam d Y) :
    MonotoneOn (fun z => quadratic lam z-Y z) (Icc zStart zEnd) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    ((by unfold quadratic; fun_prop : ContinuousOn (quadratic lam) (Icc zStart zEnd)).sub (continuation_continuous hY))
    (f' := fun z => lam-z-vectorField lam d z (Y z))
  · intro z hz
    exact ((quadratic_hasDerivAt lam z).hasDerivWithinAt.sub
      (hY.2 z (interior_subset hz))).mono interior_subset
  · intro z _
    exact sub_nonneg.mpr (vectorField_le_line lam d z (Y z))

/-- The single terminal split q=.27 propagates the root budget backwards
through the entire continuation interval. -/
theorem Admissible.continuation_above_root_budget {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {Y : ℝ → ℝ} (hY : IsContinuation lam d Y)
    (hp : PassesTerminalTests lam d Y) {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    quadratic lam z-quadratic lam 1+0.019 < Y z := by
  have he := hp zEnd (by norm_num [zTest, zEnd]) (0.27 : ℝ) (by norm_num [qLo, qHi])
  have ht := Certificates.Compact.terminal_above_root_budget lam d.S zEnd
    hd.compact_lambdaRange hd.compact_scalarRange (by norm_num [zEnd])
  change 0.019 < terminalBound lam d.S zEnd 0.27-(quadratic lam zEnd-quadratic lam 1) at ht
  have hm := continuation_defect_monotone hY hz (by norm_num [zStart, zEnd]) hz.2
  linarith

theorem Admissible.control_binary_gap {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) :
    0.01446 < lam * primitive lam d c.1-c.1*(quadratic lam (1-c.1)-d.S) := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    have hp := hc.1
    norm_num [pLo, pHi] at hp ⊢
    exact hp
  have hR := hd.primitive_lower (show c.1 ∈ Icc pLo zStart from
    ⟨hc.1.1, hc.1.2.trans (by norm_num [pHi, zStart])⟩)
  exact Certificates.Compact.opposite_binary_gt lam d.S c.1 (primitive lam d c.1)
    hd.compact_lambdaRange hd.compact_scalarRange hp hR

theorem Admissible.determinant_le_three {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) :
    controlDeterminant lam d c ≤ 3 := by
  have hR0 := hd.control_R_lower hc.1
  have hR1 := hd.control_R_upper hc.1
  have hP := hd.control_P_bounds hc.1
  have hl := hd.1
  have hp := hc.1
  have hx := hc.2.1
  have hy := hc.2.2
  have hy0 := (le_max_left xLo c.1).trans hy.1
  norm_num [lambdaLo, lambdaHi, pLo, pHi, xLo, xHi] at hl hp hx hy hy0
  have hh : 2*lam-c.2.1 ≤ 1 := by linarith [hl.2, hx.1]
  have hk : -1 ≤ c.1+c.2.2-lam := by linarith [hp.1, hy0, hl.2]
  have h1 := mul_nonneg (sub_nonneg.mpr hh)
    (show 0 ≤ primitive lam d c.1 by linarith)
  have h2 := mul_nonneg (show 0 ≤ c.1+c.2.2-lam+1 by linarith) hP.1
  unfold controlDeterminant
  nlinarith [hP.2]

/-- The strict binary gap forces a positive state coefficient on every control
within 10⁻⁴ of the line branch, with no low-rank regularity hypothesis. -/
theorem Admissible.near_line_alpha_positive {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain) {z u : ℝ}
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    (hfx : d.phi c.2.1 ≤ lam-c.2.1) (hfy : d.phi c.2.2 ≤ lam-c.2.2)
    (hnear : controlH lam d z u c ≤ lam-z+1/10000) :
    0 < controlAlpha lam d c := by
  let R := primitive lam d c.1
  let P := quadratic lam (1-c.1)-d.S
  let N := R*d.phi c.2.1+P*d.phi c.2.2
  let A := (c.1+c.2.2-lam)*d.phi c.2.1+(2*lam-c.2.1)*d.phi c.2.2
  let D := controlDeterminant lam d c
  let K := quadratic lam (z-c.1)-d.S-u
  have hD : 0 < D := lt_trans (by norm_num) (hd.determinant_positive hc)
  have hDmax : D ≤ 3 := hd.determinant_le_three hc
  have hR0 : 0 ≤ R := by dsimp [R]; linarith [hd.control_R_lower hc.1]
  have hP0 : 0 ≤ P := (hd.control_P_bounds hc.1).1
  have hg := hd.control_binary_gap hc
  have hx := mul_nonneg hR0 (sub_nonneg.mpr hfx)
  have hy := mul_nonneg hP0 (sub_nonneg.mpr hfy)
  have hgap : 0.01446 < D-N := by
    dsimp [D, N, R, P] at *
    unfold controlDeterminant
    nlinarith
  have hU : (0.2 : ℝ) ≤ z-lam := by
    have hzl := hz.1
    have hlu := hd.1.2
    norm_num [zStart, lambdaHi] at hzl hlu
    linarith
  have hK : 0 ≤ K := (hd.control_K_bounds hc.1 hz huLow huHigh).1
  have hnear' : -((z-lam)*N+K*A) ≤ (lam-z+1/10000)*D := by
    apply (div_le_iff₀ hD).mp
    exact hnear
  have hA : 0 < A := by
    by_contra hn
    have hprod := mul_nonpos_of_nonneg_of_nonpos hK (le_of_not_gt hn)
    have hgprod := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ D-N by linarith)
    nlinarith
  exact div_pos hA hD

end OptimalG.Variational
