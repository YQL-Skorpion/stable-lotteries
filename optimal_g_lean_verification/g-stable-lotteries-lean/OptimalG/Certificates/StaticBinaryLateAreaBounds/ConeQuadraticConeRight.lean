import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.StaticBinaryLateAreaModels.ConeQuadraticConeRight
import OptimalG.Certificates.StaticBinaryData.LateBatch004

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeRight
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000)) (hr : q+d∈Icc (348541/1000000) (849/2000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaQuadratic q) (hupper : upper (q+d)≤upperRight (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.ConeQuadraticConeRight.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.ConeQuadraticConeRight.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.ConeQuadraticConeRight.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.ConeQuadraticConeRight.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (7/80) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticConeRight.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.ConeQuadraticConeRight.numerator d q 0 := StaticBinaryData.LateArea.ConeQuadraticConeRightLeaf000.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.ConeQuadraticConeRight.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticConeRight
