import OptimalG.Certificates.StaticHighBounds
import OptimalG.Certificates.StaticBinaryCapControl

namespace OptimalG.Certificates.StaticBinaryInputs
open Set

theorem terminal_bound {p q : ℝ} (hp : p∈Icc (21/25:ℝ) (7/8))
    (hq : q∈Icc (26/100:ℝ) (28/100)) :
    Variational.terminalBound StaticLow.lam StaticLow.slack p q≤Y p := by
  have hq' : q∈Icc (13/50:ℝ) (7/25) := by
    constructor <;> linarith only [hq.1,hq.2]
  by_cases hc : p≤(StaticHigh.contact:ℝ)
  · rw [←actual hc,StaticCurve.high_primitive
      (by norm_num [StaticLow.lam]; linarith only [hp.1])]
    exact StaticHighData.terminal_bound ⟨hp.1,hc⟩ hq'
  · rw [after_contact (le_of_not_ge hc)]
    exact StaticTerminal.terminal_le_parabola hp hq'

theorem early_deficit {p : ℝ} (hp : p∈Icc (31/40:ℝ) (807/1000)) :
    Variational.quadratic StaticLow.lam p-StaticLow.slack-Y p≤
      (399/500)*(max (p-391/500) 0)^2 := by
  have hc : p≤(StaticHigh.contact:ℝ) := hp.2.trans (by norm_num [StaticHigh.contact])
  rw [←actual hc,StaticCurve.high_primitive
    (by norm_num [StaticLow.lam]; linarith only [hp.1])]
  exact StaticHighData.early_deficit
    ⟨by norm_num [StaticLow.lam]; linarith only [hp.1],hc⟩

end OptimalG.Certificates.StaticBinaryInputs
