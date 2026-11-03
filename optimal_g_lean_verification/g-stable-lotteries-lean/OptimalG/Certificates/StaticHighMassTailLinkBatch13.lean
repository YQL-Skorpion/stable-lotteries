import OptimalG.Certificates.HighMassTailCoverage.Batch002
import OptimalG.Certificates.StaticHighMassTailDataBatch07
import OptimalG.Certificates.StaticHighMassTailDataBatch08
import OptimalG.Certificates.StaticHighMassTailDataBatch09


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Head
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Head
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (1/20) (527/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper0Head.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper0Head.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper0Head.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper0Head.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper0Head.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper0Head.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper0Head.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper0Head.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (627/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0HeadLeaf003.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Head


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Cap
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cap
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (527/2000) (313/1000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper0Cap.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper0Cap.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper0Cap.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper0Cap.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper0Cap.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper0Cap.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper0Cap.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper0Cap.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Cap.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Cap.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (527/2000) (313/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Cap.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Cap.nonpos
    · linarith only [hr.2]
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0CapLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0CapLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Cap


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Cone
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Cone
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (313/1000) (7/20))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper0Cone.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper0Cone.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper0Cone.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper0Cone.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper0Cone.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper0Cone.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper0Cone.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper0Cone.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.CurvedUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0ConeLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0ConeLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Cone


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0NearLine
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0NearLine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (7/20) (9/25))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper0NearLine.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper0NearLine.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper0NearLine.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper0NearLine.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper0NearLine.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper0NearLine.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper0NearLine.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper0NearLine.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (7/20) (9/25) := by
      simpa [HighMassTailCoverage.CurvedUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0NearLine.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0NearLineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0NearLineLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0NearLine


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Line
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.CurvedUpper0Line
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (9/25) (1227/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.CurvedUpper0Line.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.CurvedUpper0Line.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.CurvedUpper0Line.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.CurvedUpper0Line.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.CurvedUpper0Line.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.CurvedUpper0Line.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.CurvedUpper0Line.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.CurvedUpper0Line.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (1583/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1583/2000) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf006.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (391/500) (801/1000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf008.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf008.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf009.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf009.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf010.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf010.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (1621/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf011.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf011.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf012.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf012.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf013.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf013.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1621/2000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.CurvedUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf014.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.CurvedUpper0LineLeaf014.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (801/1000) (41/50) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.CurvedUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.CurvedUpper0Line
