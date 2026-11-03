import OptimalG.Certificates.HighMassTailCoverage.Batch001
import OptimalG.Certificates.StaticHighMassTailDataBatch04
import OptimalG.Certificates.StaticHighMassTailDataBatch05
import OptimalG.Certificates.StaticHighMassTailDataBatch06
import OptimalG.Certificates.StaticHighMassTailDataBatch07


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Head
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Head
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (1/20) (527/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper1Head.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper1Head.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper1Head.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper1Head.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper1Head.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper1Head.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper1Head.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper1Head.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (627/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (1681/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (1531/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (1531/2000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) (797/800) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf007.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1HeadLeaf007.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1531/2000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Head


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Cap
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cap
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (527/2000) (313/1000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper1Cap.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper1Cap.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper1Cap.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper1Cap.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper1Cap.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper1Cap.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper1Cap.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper1Cap.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (1153/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1153/4000) (313/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1CapLeaf006.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Cap


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Cone
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Cone
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (313/1000) (7/20))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper1Cone.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper1Cone.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper1Cone.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper1Cone.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper1Cone.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper1Cone.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper1Cone.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper1Cone.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (683/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1289/4000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (663/2000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf006.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf007.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf007.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) (797/800) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf008.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf008.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (2897/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (2541/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (2897/4000) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (2541/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf010.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf010.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (2541/8000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf011.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf011.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (293/400) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf012.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf012.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1289/4000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf013.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf013.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf014.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf014.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (663/2000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf015.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1ConeLeaf015.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Cone


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1NearLine
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1NearLine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (7/20) (9/25))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper1NearLine.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper1NearLine.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper1NearLine.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper1NearLine.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper1NearLine.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper1NearLine.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper1NearLine.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper1NearLine.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (7/20) (9/25) := by
      simpa [HighMassTailCoverage.MiddleUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1NearLine.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1NearLineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1NearLineLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1NearLine


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Line
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper1Line
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (9/25) (1227/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper1Line.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper1Line.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper1Line.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper1Line.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper1Line.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper1Line.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper1Line.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper1Line.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper1LineLeaf006.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper1Line
