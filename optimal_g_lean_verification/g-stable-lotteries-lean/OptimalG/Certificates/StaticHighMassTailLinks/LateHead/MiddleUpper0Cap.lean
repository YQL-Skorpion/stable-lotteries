import OptimalG.Certificates.HighMassTailCoverage.Batch000
import OptimalG.Certificates.StaticHighMassTailData.LateHead.MiddleUpper0Cap

namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Cap
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Cap
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (527/2000) (313/1000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper0Cap.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper0Cap.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper0Cap.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper0Cap.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper0Cap.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper0Cap.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper0Cap.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper0Cap.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1153/4000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0CapLeaf006.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Cap
