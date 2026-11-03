import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticHead
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000)) (hr : q+d∈Icc 0 (527/2000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaQuadratic q) (hupper : upper (q+d)≤areaHead (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.ConeQuadraticHead.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.ConeQuadraticHead.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.ConeQuadraticHead.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.ConeQuadraticHead.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (7/80) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticHead.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (9764675264432828020717332009213874188106300418835385927801144446371126129006862927848715177742693160316714351616160693891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000) := by
      simpa [StaticBinaryLateCoverage.ConeQuadraticHead.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.ConeQuadraticHead
