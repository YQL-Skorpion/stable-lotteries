import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch02
import OptimalG.Certificates.HighMassTailCoverage.Batch000
import OptimalG.Certificates.StaticHighMassTailDataBatch03
import OptimalG.Certificates.StaticHighMassTailDataBatch04


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower1HighForwardKink
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower1HighForwardKink
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower1HighForwardKinkLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) 1)
    (hs : Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0) : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z hs] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower1HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Head
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Head
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (1/20) (527/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper0Head.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper0Head.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper0Head.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper0Head.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper0Head.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper0Head.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper0Head.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper0Head.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1/20) (627/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (627/4000) (1681/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (749/1000) (1531/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (1531/2000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) (797/800) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Head.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf007.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0HeadLeaf007.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (1531/2000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1681/8000) (527/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Head.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Head


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Cone
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Cone
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (313/1000) (7/20))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper0Cone.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper0Cone.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper0Cone.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper0Cone.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper0Cone.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper0Cone.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper0Cone.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper0Cone.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (683/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (683/1000) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1289/4000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (663/2000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf006.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf007.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf007.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) (797/800) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf008.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf008.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (2897/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (2541/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    exfalso
    rcases hbp with ⟨hpl,hpu⟩
    rcases hbz with ⟨hzl,hzu⟩
    rcases hbr with ⟨hrl,hru⟩
    rcases hq with ⟨hql,hqu⟩
    linarith only [hpl,hpu,hzl,hzu,hrl,hru,hql,hqu]
  · have hbp : p∈Icc (2897/4000) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (2541/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf010.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf010.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (293/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (797/800) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (2541/8000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf011.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf011.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (293/400) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (1289/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf012.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf012.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1289/4000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf013.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf013.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (313/1000) (663/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf014.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf014.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (663/2000) (7/20) := by
      simpa [HighMassTailCoverage.MiddleUpper0Cone.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Cone.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf015.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0ConeLeaf015.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Cone


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0NearLine
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0NearLine
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (7/20) (9/25))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper0NearLine.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper0NearLine.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper0NearLine.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper0NearLine.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper0NearLine.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper0NearLine.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper0NearLine.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper0NearLine.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (7/20) (9/25) := by
      simpa [HighMassTailCoverage.MiddleUpper0NearLine.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0NearLine.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0NearLineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0NearLineLeaf000.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0NearLine


namespace OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Line
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.LateHead.MiddleUpper0Line
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bound {p z r : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    (hr : r∈Icc (9/25) (1227/2000))
    (hq : p-z+r∈Icc (1/20:ℝ) (527/2000)) : StaticHighMassTailModels.LateHead.MiddleUpper0Line.target p z r≤0 := by
  have hx : ∀ i,(HighMassTailCoverage.MiddleUpper0Line.rootBox i).Contains (![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] i) := by
    intro i
    fin_cases i
    · simpa [HighMassTailCoverage.MiddleUpper0Line.rootBox,RatInterval.Contains] using hlam
    · simpa [HighMassTailCoverage.MiddleUpper0Line.rootBox,RatInterval.Contains] using hS
    · simpa [HighMassTailCoverage.MiddleUpper0Line.rootBox,RatInterval.Contains] using hp
    · simpa [HighMassTailCoverage.MiddleUpper0Line.rootBox,RatInterval.Contains] using hz
    · simpa [HighMassTailCoverage.MiddleUpper0Line.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := HighMassTailCoverage.MiddleUpper0Line.covered ![(StaticLow.lam:ℝ),(StaticLow.slack:ℝ),p,z,r] hx
  fin_cases j
  · have hbp : p∈Icc (13/20) (179/250) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf000.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf000.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (97/100) (197/200) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf001.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf001.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (749/1000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf002.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf002.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) (397/400) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf003.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf003.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (9/25) (3387/8000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf004.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf004.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (749/1000) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (397/400) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (3387/8000) (1947/4000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf005.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf005.denominator_pos hlam hS hbp hbz hbr
  · have hbp : p∈Icc (179/250) (391/500) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 2
    have hbz : z∈Icc (197/200) 1 := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 3
    have hbr : r∈Icc (1947/4000) (1227/2000) := by
      simpa [HighMassTailCoverage.MiddleUpper0Line.leafBoxes,RatInterval.Contains] using hj 4
    apply StaticHighMassTailModels.LateHead.MiddleUpper0Line.nonpos
    · exact (StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf006.numerator_pos hlam hS hbp hbz hbr).le
    · exact StaticHighMassTailData.LateHead.MiddleUpper0LineLeaf006.denominator_pos hlam hS hbp hbz hbr
end OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Line
