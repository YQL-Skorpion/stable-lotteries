import OptimalG.UniversalLPData.Stages
import OptimalG.UniversalControlBoxes

/-! The checked universal LP yields the scalar input bounds for every necessary
activation on the full parameter interval. This module is built only after all
numerical dual certificates and the sequential stage checks have completed. -/
namespace OptimalG

namespace NormalizedNecessaryConditions
variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions lam phi)
include h

theorem universal_lp_primitive_bounds (hL : Certificates.Compact.LambdaRange lam) :
    UniversalLPPrimitiveBounds phi := by
  have hcap : lam ≤ (UniversalLP.L : ℝ) := by
    calc
      lam ≤ (0.562330 : ℝ) := hL.2
      _ = (UniversalLP.L : ℝ) := by norm_num [UniversalLP.L]
  have hc := h.mono hcap
  have hcentral := UniversalLP.Data.central_bound hc
  have hhalflo := UniversalLP.Data.envelope4_bound hc
  have hhalfhi := UniversalLP.Data.envelope5_bound hc
  have hcnum : (-0.001429898539474 : ℝ) ≤ (UniversalLP.Data.central.bound : ℝ) := by
    change (-0.001429898539474 : ℝ) ≤
      ((-893686587170745658497841277055894957 /
        625000000000000000000000000000000000000 : ℚ) : ℝ)
    norm_num
  have hlonum : (0.1295146851195648 : ℝ) ≤ (UniversalLP.Data.envelope4.bound : ℝ) := by
    change (0.1295146851195648 : ℝ) ≤
      ((4047333909986401187524368329353783319 /
        31250000000000000000000000000000000000 : ℚ) : ℝ)
    norm_num
  have hhinum : (-0.1342007783259218 : ℝ) ≤ (UniversalLP.Data.envelope5.bound : ℝ) := by
    change (-0.1342007783259218 : ℝ) ≤
      ((-204774136849856206381957749 / 1525878906250000000000000000 : ℚ) : ℝ)
    norm_num
  norm_num at hcentral hhalflo hhalfhi
  constructor
  · convert hcnum.trans hcentral using 1 <;> norm_num <;> rfl
  · convert hlonum.trans hhalflo using 1 <;> norm_num <;> rfl
  · norm_num
    linarith

end NormalizedNecessaryConditions
end OptimalG
