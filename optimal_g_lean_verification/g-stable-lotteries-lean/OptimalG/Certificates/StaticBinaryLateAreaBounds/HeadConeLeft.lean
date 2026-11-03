import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.StaticBinaryLateAreaModels.HeadConeLeft
import OptimalG.Certificates.StaticBinaryData.LateBatch001

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadConeLeft
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc 0 (527/2000)) (hr : q+d∈Icc (2950935005377889/10000000000000000) (348541/1000000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaHead q) (hupper : upper (q+d)≤upperLeft (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.HeadConeLeft.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.HeadConeLeft.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.HeadConeLeft.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.HeadConeLeft.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (7/80) := by
      simpa [StaticBinaryLateCoverage.HeadConeLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (527/2000) := by
      simpa [StaticBinaryLateCoverage.HeadConeLeft.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.HeadConeLeft.numerator d q 0 := StaticBinaryData.LateArea.HeadConeLeftLeaf000.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.HeadConeLeft.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadConeLeft
