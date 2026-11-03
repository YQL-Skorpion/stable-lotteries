import OptimalG.ParameterTransfer
import OptimalG.Certificates.TransportTerminal
import OptimalG.VariationalLogDeficit

/-! The actual transferred competitor satisfies the cap-relaxed terminal
obstacle used by the reference logarithmic certificate. The positive transfer
margin is retained and can be dropped only at the final comparison. -/
namespace OptimalG.Variational
open Set Real

namespace ParameterTransfer

theorem shifted_plateau_closed {lam delta r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r∈Icc tEnd zStart) :
    shiftedPrimitive lam d delta r=quadratic (lam+delta) r-scalar d.S delta := by
  rw [shiftedPrimitive_eq lam delta d
    ⟨(by norm_num [pLo,tEnd] : pLo≤tEnd).trans hr.1,hr.2⟩]
  exact shifted_flat ((by norm_num [tEnd] : (0.38:ℝ)≤tEnd).trans hr.1)
    (primitive_plateau_closed hd hr.1)

theorem UpwardTransfer.standard_terminal_margin {lam delta : ℝ} {d : LowRankData}
    {Y : ℝ→ℝ} (T : UpwardTransfer lam delta d Y)
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) {z q : ℝ} (hz : z∈Icc zTest zEnd) (hq : q∈Icc qLo qHi) :
    terminalBound (lam+delta) (scalar d.S delta) z q+0.07812*delta≤T.trajectory z := by
  have hz' : z∈Icc (0.84:ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zTest,zEnd]
  have hq' : q∈Icc (0.26:ℝ) 0.28 := by convert! hq using 1 <;> norm_num [qLo,qHi]
  have hr : 1-z+q∈Icc tEnd zStart := by
    constructor <;> norm_num [tEnd,zStart] <;> linarith [hz'.1,hz'.2,hq'.1,hq'.2]
  have hqLow : q∈Icc pLo tEnd := by
    constructor <;> norm_num [pLo,tEnd] <;> linarith [hq'.1,hq'.2]
  have hcap := shifted_cap_bound hd hdelta hqLow
  have hT := T.terminal z hz q hq
  rw [shifted_plateau_closed hd hr] at hT
  have hden : 0<lam+delta-q := by linarith [hL.1,hq'.2]
  have hnum : z*(quadratic (lam+delta) (1-z+q)-scalar d.S delta-
      cap (lam+delta) (scalar d.S delta) q)≤
      z*(quadratic (lam+delta) (1-z+q)-scalar d.S delta-
        shiftedPrimitive lam d delta q) :=
    mul_le_mul_of_nonneg_left (by linarith only [hcap]) (by linarith [hz'.1])
  have hdiv := div_le_div_of_nonneg_right hnum hden.le
  unfold terminalBound
  linarith only [hdiv,hT]

end ParameterTransfer

theorem transferred_terminal_log_feasibility {lam delta M z q : ℝ} {d : LowRankData}
    {Y : ℝ→ℝ} (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (hz : z∈Icc zTest zEnd) (hq : q∈Icc qLo qHi)
    (hpos : 0<M-ParameterTransfer.scalar d.S delta-T.trajectory z) :
    log (M-ParameterTransfer.scalar d.S delta-T.trajectory z)≤
      log (M-ParameterTransfer.scalar d.S delta-
        terminalBound (lam+delta) (ParameterTransfer.scalar d.S delta) z q) := by
  have hT := T.standard_terminal_margin hd hL hdelta hz hq
  apply log_le_log hpos
  have hg : 0≤(0.07812:ℝ)*delta := by positivity
  linarith

/-- Direct interpretation of the finite terminal certificate for the actual
transferred continuation and its scalar-dependent terminal warp. -/
theorem transferred_terminal_certificate_feasibility
    {lam delta : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (p : Certificates.Transport.TerminalParameters)
    (hlam : (p.lam:ℝ)=lam+delta)
    (hz : (p.highRank:ℝ)-(ParameterTransfer.scalar d.S delta-p.slack)∈Icc zTest zEnd)
    (hq : (p.lowRank:ℝ)∈Icc qLo qHi)
    (hpos : 0<(p.level:ℝ)-ParameterTransfer.scalar d.S delta-
      T.trajectory ((p.highRank:ℝ)-(ParameterTransfer.scalar d.S delta-p.slack))) :
    log ((p.level:ℝ)-ParameterTransfer.scalar d.S delta-
      T.trajectory ((p.highRank:ℝ)-(ParameterTransfer.scalar d.S delta-p.slack)))≤
      log (p.terminalDeficit (ParameterTransfer.scalar d.S delta)) := by
  have h := transferred_terminal_log_feasibility T hd hL hdelta hz hq hpos
  convert h using 1
  simp only [Certificates.Transport.TerminalParameters.terminalDeficit,terminalBound,hlam,
    Certificates.quadratic,quadratic,Certificates.cap,cap]

end OptimalG.Variational
