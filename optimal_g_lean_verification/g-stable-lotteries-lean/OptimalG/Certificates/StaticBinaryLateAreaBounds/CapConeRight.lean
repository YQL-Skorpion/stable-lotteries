import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.StaticBinaryLateAreaModels.CapConeRight
import OptimalG.Certificates.StaticBinaryData.LateBatch002

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.CapConeRight
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (527/2000) (2950935005377889/10000000000000000)) (hr : q+d∈Icc (348541/1000000) (849/2000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaCap q) (hupper : upper (q+d)≤upperRight (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.CapConeRight.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.CapConeRight.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.CapConeRight.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.CapConeRight.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (7/80) := by
      simpa [StaticBinaryLateCoverage.CapConeRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (527/2000) (2950935005377889/10000000000000000) := by
      simpa [StaticBinaryLateCoverage.CapConeRight.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.CapConeRight.numerator d q 0 := StaticBinaryData.LateArea.CapConeRightLeaf000.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.CapConeRight.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.CapConeRight
