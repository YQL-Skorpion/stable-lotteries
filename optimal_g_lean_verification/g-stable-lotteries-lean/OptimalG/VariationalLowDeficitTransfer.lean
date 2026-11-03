import OptimalG.ParameterTransferLowData

/-! The low-rank deficits used by the transport localization improve under
the actual upward parameter transfer. No reverse ODE estimate is needed for
these low-rank quantities. -/
namespace OptimalG.Variational
open Set ParameterTransfer

theorem transferred_low_lipschitz {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    LipschitzOnWith (1/3:NNReal) (shiftedPrimitive lam d delta) (Icc ell xHi) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have hat : a∈Icc ell tEnd := ⟨ha.1,ha.2.trans (by norm_num [xHi,tEnd])⟩
  have hbt : b∈Icc ell tEnd := ⟨hb.1,hb.2.trans (by norm_num [xHi,tEnd])⟩
  have hh := hd.lowPrimitive_lipschitz.dist_le_mul a hat b hbt
  have he : shiftedPrimitive lam d delta a-shiftedPrimitive lam d delta b=
      lowPrimitive lam d a-lowPrimitive lam d b := by
    rw [shifted_low_increment hd hb ha,hd.lowPrimitive_sub hbt hat]
  simpa only [Real.dist_eq,he] using hh

theorem transferred_cap_gap_ge {lam delta r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hdelta : 0≤delta) (hr : r∈Icc pLo tEnd) :
    cap lam d.S r-primitive lam d r≤
      cap (lam+delta) (scalar d.S delta) r-shiftedPrimitive lam d delta r := by
  rw [shiftedPrimitive_eq lam delta d ⟨hr.1,hr.2.trans (by norm_num [tEnd,zStart])⟩]
  have hh := cap_gain_lower hd.compact_lambdaRange
    (by convert! hd.slack_upper using 1 <;> norm_num) hdelta
    (by convert! hr using 1 <;> norm_num [pLo,tEnd])
  dsimp only [shifted]
  nlinarith only [hh,mul_nonneg (by norm_num : (0:ℝ)≤0.338) hdelta]

theorem transferred_root_slack_eq {lam delta r : ℝ} {d : LowRankData}
    (hr : r∈Icc pLo xHi) :
    scalar d.S delta-quadratic (lam+delta) r+shiftedPrimitive lam d delta r=
      d.S-quadratic lam r+primitive lam d r+delta*(0.38-r) := by
  rw [shiftedPrimitive_eq lam delta d ⟨hr.1,hr.2.trans (by norm_num [xHi,zStart])⟩]
  dsimp only [shifted]
  rw [gain_before (by convert! hr.2 using 1 <;> norm_num [xHi])]
  unfold scalar quadratic
  ring

theorem transferred_root_slack_ge {lam delta r : ℝ} {d : LowRankData}
    (hdelta : 0≤delta) (hr : r∈Icc pLo xHi) :
    d.S-quadratic lam r+primitive lam d r≤
      scalar d.S delta-quadratic (lam+delta) r+shiftedPrimitive lam d delta r := by
  rw [transferred_root_slack_eq hr]
  have hh := mul_nonneg hdelta
    (show 0≤(0.38:ℝ)-r by have h := hr.2; norm_num [xHi] at h;linarith)
  linarith only [hh]

end OptimalG.Variational
