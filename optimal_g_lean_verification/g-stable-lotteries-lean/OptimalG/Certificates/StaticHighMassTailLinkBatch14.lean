import OptimalG.Certificates.HighMassTailCoverage.Batch003
import OptimalG.Certificates.StaticHighMassTailDataBatch10
import OptimalG.Certificates.StaticHighMassTailDataBatch11


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Head
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper1Head
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (1/20) (527/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper1Head.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper1Head.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper1Head.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper1Head.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper1Head.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper1Head.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper1Head.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper1Head.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (627/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1HeadLeaf003.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Head


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Cap
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper1Cap
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (527/2000) (313/1000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper1Cap.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper1Cap.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper1Cap.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper1Cap.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper1Cap.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper1Cap.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper1Cap.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper1Cap.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1CapLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1CapLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Cap


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Cone
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper1Cone
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (313/1000) (7/20))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper1Cone.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper1Cone.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper1Cone.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper1Cone.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper1Cone.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper1Cone.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper1Cone.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper1Cone.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.CurvedUpper1Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1ConeLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1ConeLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Cone


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1NearLine
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper1NearLine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (7/20) (9/25))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper1NearLine.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper1NearLine.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper1NearLine.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper1NearLine.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper1NearLine.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper1NearLine.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper1NearLine.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper1NearLine.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (7/20) (9/25) := by
      simpa [HighMassTailCoverage.CurvedUpper1NearLine.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1NearLine.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1NearLineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1NearLineLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1NearLine


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Line
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper1Line
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (9/25) (1227/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper1Line.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper1Line.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper1Line.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper1Line.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper1Line.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper1Line.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper1Line.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper1Line.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf006.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf008.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf008.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf009.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf009.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf010.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf010.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf011.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf011.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf012.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf012.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf013.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf013.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper1Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf014.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper1LineLeaf014.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper1Line.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper1Line
