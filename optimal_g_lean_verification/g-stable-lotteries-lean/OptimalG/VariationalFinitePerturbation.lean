import OptimalG.VariationalActiveTerminal
import OptimalG.VariationalStateBounds

/-!
# Exact finite perturbations for the active-rank argument

Lowering S and shifting the high state by the same positive amount preserves K.
An exact rational identity then supplies the comparison used in Appendix B.3,
without differentiating a family of averaged ODEs.
-/

namespace OptimalG.Certificates.Control

 theorem value_RP_difference (U h k R P K A B dR dP : ℝ)
    (hD : det h k R P ≠ 0) (hDn : det h k (R+dR) (P+dP) ≠ 0) :
    value U h k (R+dR) (P+dP) K A B-value U h k R P K A B =
      alphaNumerator h k A B*(cy U h P K*dR-cx U k R K*dP)/
        (det h k R P*det h k (R+dR) (P+dP)) := by
  unfold value
  field_simp
  unfold det cx cy alphaNumerator
  ring

 theorem value_RP_shift_nondecreasing (U h k R P K A B dR q v : ℝ)
    (hD : 0 < det h k R P) (hDn : 0 < det h k (R+dR) (P+q))
    (hA : 0 ≤ alphaNumerator h k A B) (hcy : 0 ≤ cy U h P K)
    (hq : 0 ≤ q) (hdR : v*q ≤ dR) (hratio : cx U k R K ≤ v*cy U h P K) :
    value U h k R P K A B ≤ value U h k (R+dR) (P+q) K A B := by
  have hc : 0 ≤ cy U h P K*dR-cx U k R K*q := by
    have h1 := mul_le_mul_of_nonneg_left hdR hcy
    have h2 := mul_le_mul_of_nonneg_right hratio hq
    nlinarith
  have hh := div_nonneg (mul_nonneg hA hc) (mul_pos hD hDn).le
  rw [← value_RP_difference U h k R P K A B dR q hD.ne' hDn.ne'] at hh
  exact sub_nonneg.mp hh

end OptimalG.Certificates.Control

namespace OptimalG.Variational
open Set MeasureTheory

/-- Exact scalar dependence of the terminal obstacle. -/
theorem terminalBound_slack_decrease (lam S z r q : ℝ) (hr : r ≠ 1) (hlr : lam ≠ r) :
    terminalBound lam (S-q) z r-terminalBound lam S z r =
      q*(z*(1-r-lam)/((lam-r)*(1-r))) := by
  have hr' : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  have hlr' : lam-r ≠ 0 := sub_ne_zero.mpr hlr
  unfold terminalBound cap
  field_simp
  ring

/-- Every terminal obstacle rises by strictly less than .765 times the amount
by which the continuation is shifted. -/
theorem terminalBound_slack_decrease_bound {lam S z r q : ℝ}
    (hlam : lam ∈ Icc lambdaLo lambdaHi) (hz : z ∈ Icc zTest zEnd)
    (hr : r ∈ Icc qLo qHi) (hq : 0 ≤ q) :
    terminalBound lam (S-q) z r ≤ terminalBound lam S z r+0.765*q := by
  have hL : Certificates.Compact.LambdaRange lam := by
    norm_num [Certificates.Compact.LambdaRange, lambdaLo, lambdaHi] at hlam ⊢
    exact hlam
  have hz' : z ∈ Icc (0.84 : ℝ) 0.875 := by
    norm_num [zTest, zEnd] at hz ⊢
    exact hz
  have hr' : r ∈ Icc (0.26 : ℝ) 0.28 := by
    norm_num [qLo, qHi] at hr ⊢
    exact hr
  have hrne : r ≠ 1 := by linarith [hr'.2]
  have hlrne : lam ≠ r := by linarith [hL.1, hr'.2]
  have hb := Certificates.Compact.barrier_scalar_slope_bound lam r z hL hr' hz'
  have hh := mul_le_mul_of_nonneg_left hb.le hq
  rw [← terminalBound_slack_decrease lam S z r q hrne hlrne] at hh
  linarith

/-- A fixed-state comparison sufficient for the active-rank perturbation.
If decreasing S by q lifts the continuation by q, it creates a strict uniform
terminal margin, contradicting minimality at an interior parameter. -/
theorem no_slack_decrease_with_shifted_continuation
    {lam q : ℝ} {d d' : LowRankData}
    (hd : Admissible lam d) (hd' : Admissible lam d') (hl : lambdaLo < lam) (hq : 0 < q)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hS : d'.S = d.S-q)
    (hshift : ∀ z ∈ Icc zStart zEnd, continuation lam d z+q ≤ continuation lam d' z) : False := by
  apply minimizer_no_strict_terminal_margin hd' hl hmin
  refine ⟨0.235*q, by positivity, ?_⟩
  intro z hz r hr
  have hz' : z ∈ Icc zStart zEnd :=
    ⟨(by norm_num [zStart, zTest] : zStart ≤ zTest).trans hz.1, hz.2⟩
  have hb := terminalBound_slack_decrease_bound (S := d.S) hd.1 hz hr hq.le
  rw [← hS] at hb
  linarith [hpass z hz r hr, hshift z hz']

/-- Scalar comparison turns a direct field inequality along the shifted old
trajectory into the continuation shift needed above. -/
theorem Admissible.continuation_shift_of_field_comparison
    {lam q : ℝ} {d d' : LowRankData} (hd' : Admissible lam d')
    (hS : d'.S = d.S-q)
    (hfield : ∀ z ∈ Icc zStart zEnd,
      vectorField lam d z (continuation lam d z) ≤
        vectorField lam d' z (continuation lam d z+q))
    (hd : Admissible lam d) :
    ∀ z ∈ Icc zStart zEnd, continuation lam d z+q ≤ continuation lam d' z := by
  apply scalar_ode_comparison (vectorField lam d') (19/2)
    (fun z => continuation lam d z+q) (continuation lam d')
    (fun z => vectorField lam d z (continuation lam d z))
    (fun z => vectorField lam d' z (continuation lam d' z)) zStart zEnd
    (fun z _ => hd'.vectorField_lipschitz z)
    ((continuation_continuous hd.isContinuation).add_const q)
    (continuation_continuous hd'.isContinuation)
    (fun z hz => hd.isContinuation.right_derivative hz |>.add_const q)
    (fun z hz => hd'.isContinuation.right_derivative hz)
    (fun z hz => hfield z ⟨hz.1, hz.2.le⟩) (fun _ _ => le_rfl)
  rw [hd.isContinuation.1, hd'.isContinuation.1, hS]
  linarith

end OptimalG.Variational
