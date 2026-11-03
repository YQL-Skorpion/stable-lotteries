import OptimalG.Certificates.StaticBinaryLateCoverage
import OptimalG.Certificates.StaticBinaryLateExpressions
import OptimalG.Certificates.StaticBinaryLateAreaModels.HeadCap
import OptimalG.Certificates.StaticBinaryData.LateBatch000

namespace OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadCap
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem bound {d q : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80))
    (hq : q∈Icc 0 (527/2000)) (hr : q+d∈Icc (527/2000) (2950935005377889/10000000000000000))
    (hql : q∈Icc (0:ℝ) (337/1000))
    (hlower : lower q=areaHead q) (hupper : upper (q+d)≤areaCap (q+d)) :
    d^2*((B-C*d)/(1-d)*(L-q)-1/2)≤lower q-upper (q+d) := by
  have hx : ∀ i,(StaticBinaryLateCoverage.HeadCap.rootBox i).Contains (![d,q] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryLateCoverage.HeadCap.rootBox,RatInterval.Contains] using hd
    · simpa [StaticBinaryLateCoverage.HeadCap.rootBox,RatInterval.Contains] using hq
  obtain ⟨j,hj⟩ := StaticBinaryLateCoverage.HeadCap.covered ![d,q] hx
  fin_cases j
  · have hbd : d∈Icc (1/50) (7/80) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc 0 (527/4000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (1/50) (43/800) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
  · have hbd : d∈Icc (43/800) (7/80) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.HeadCap.numerator d q 0 := StaticBinaryData.LateArea.HeadCapLeaf002.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.HeadCap.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (1/50) (43/800) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.HeadCap.numerator d q 0 := StaticBinaryData.LateArea.HeadCapLeaf003.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.HeadCap.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (43/800) (7/80) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (1581/8000) (3689/16000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.HeadCap.numerator d q 0 := StaticBinaryData.LateArea.HeadCapLeaf004.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.HeadCap.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (43/800) (113/1600) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (3689/16000) (527/2000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    have hn : 0<StaticBinaryLateAreaModels.HeadCap.numerator d q 0 := StaticBinaryData.LateArea.HeadCapLeaf005.numerator_pos (u:=0) hbd hbq (by constructor <;> norm_num)
    have hh := StaticBinaryLateAreaModels.HeadCap.nonneg hd hql hn
    rw [hlower]
    linarith only [hh,hupper]
  · have hbd : d∈Icc (113/1600) (7/80) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 0
    have hbq : q∈Icc (3689/16000) (527/2000) := by
      simpa [StaticBinaryLateCoverage.HeadCap.leafBoxes,RatInterval.Contains] using hj 1
    exfalso
    linarith only [hbd.1,hbd.2,hbq.1,hbq.2,hr.1,hr.2]
end OptimalG.Certificates.StaticBinaryLateAreaBounds.HeadCap
