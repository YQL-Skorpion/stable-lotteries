import OptimalG.Certificates.StaticHighTerminalTangent

namespace OptimalG.Certificates.StaticHighData
open Set

theorem terminal_bound {r q : ℝ} (hr : r∈Icc (21/25:ℝ) StaticHigh.contact)
    (hq : q∈Icc (13/50:ℝ) (7/25)) :
    Variational.terminalBound StaticLow.lam StaticLow.slack r q≤primitive r := by
  apply (StaticTerminal.terminal_le_parabola
    (show r∈Icc (21/25:ℝ) (7/8) from ⟨hr.1,hr.2.trans (by norm_num [StaticHigh.contact])⟩) hq).trans
  exact parabola_le_primitive ⟨by norm_num [StaticLow.lam]; linarith [hr.1],hr.2⟩

end OptimalG.Certificates.StaticHighData
