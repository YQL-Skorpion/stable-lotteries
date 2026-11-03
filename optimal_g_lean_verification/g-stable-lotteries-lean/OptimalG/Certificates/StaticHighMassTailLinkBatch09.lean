import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch01


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardLeft
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardLeft
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardLeftLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardLeft


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardRight
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardRight
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardRightLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardRight


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardKink
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedUpper1HighForwardKink
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedUpper1HighForwardKinkLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardKink


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower0HighCapMax
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighCapMax
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighCapMaxLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower0HighCapMax


namespace OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower0HighForwardLeft
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.FullHigh.CurvedLower0HighForwardLeft
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.FullHigh.CurvedLower0HighForwardLeftLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.FullHigh.CurvedLower0HighForwardLeft
