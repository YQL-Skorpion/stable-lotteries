import OptimalG.VariationalNumericalLocalization
import OptimalG.VariationalLowDeficitTransfer
import OptimalG.VariationalTransferQuantitative

/-! Reference bounds for the upward-transferred competitor imply the
original minimizing curve's D3 bounds. The high-rank estimate explicitly
retains the proved reverse ODE error; the two low-rank deficits only improve. -/
namespace OptimalG.Variational
open Set ParameterTransfer

theorem original_localizations_of_transferred {lam delta reference : ℝ}
    {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : delta∈Icc (0:ℝ) 0.00000003)
    (hY : IsContinuation lam d Y) (hpass : PassesTerminalTests lam d Y)
    (T : UpwardTransfer lam delta d Y)
    (href : reference∈Icc (0.29509:ℝ) 0.296)
    (hscalar : |scalar d.S delta-(2303623505254907/100000000000000000:ℝ)|<(0.000237:ℝ))
    (hinitial : cap (lam+delta) (scalar d.S delta) reference-
      shiftedPrimitive lam d delta reference<(0.000001563:ℝ))
    (hterminal : scalar d.S delta-quadratic (lam+delta) 0.34854007977695545+
      shiftedPrimitive lam d delta 0.34854007977695545<(0.000000063:ℝ))
    (hhigh : quadratic (lam+delta) (7835342428237777/10^16)-scalar d.S delta-
      T.trajectory (7835342428237777/10^16)<(0.00000006:ℝ)) :
    d.S∈Icc (0.02271790:ℝ) 0.023354 ∧
      cap lam d.S reference-lowPrimitive lam d reference<(0.00000191061404:ℝ) ∧
      d.S-quadratic lam 0.34854007977695545+lowPrimitive lam d 0.34854007977695545<
        (0.00000008688098:ℝ) ∧
      quadratic lam (7835342428237777/10^16)-d.S-Y (7835342428237777/10^16)<
        (1711874:ℝ)/10^13 := by
  have hS := upper_transport_scalar_tube
    (show delta∈Icc (0:ℝ) 0.000005 from ⟨hdelta.1,by linarith only [hdelta.2]⟩) hscalar
  have hlow := transferred_cap_gap_ge hd hdelta.1
    (r:=reference) (by constructor <;> norm_num [pLo,tEnd] <;> linarith only [href.1,href.2])
  have hre : ¬reference≤ell := by norm_num [ell];linarith only [href.1]
  have hrt : reference≤tEnd := by norm_num [tEnd];linarith only [href.2]
  rw [primitive,if_neg hre,if_pos hrt] at hlow
  have hroot := transferred_root_slack_ge (lam:=lam) (d:=d) hdelta.1
    (r:=0.34854007977695545) (by norm_num [pLo,xHi])
  rw [primitive,if_neg (by norm_num [ell] : ¬(0.34854007977695545:ℝ)≤ell),
    if_pos (by norm_num [tEnd] : (0.34854007977695545:ℝ)≤tEnd)] at hroot
  have hgap := original_high_deficit_le_transferred hd hLnew hdelta.1 hY hpass T
    (z:=7835342428237777/10^16) (by norm_num [zStart])
  refine ⟨hS,?_,?_,?_⟩ <;> linarith only [hlow,hinitial,hroot,hterminal,hgap,hhigh,hdelta.2]

end OptimalG.Variational
