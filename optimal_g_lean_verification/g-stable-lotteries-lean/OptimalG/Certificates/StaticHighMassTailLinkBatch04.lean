import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch00
import OptimalG.Certificates.StaticHighMassTailDataBatch01


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadSquare
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadSquare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadSquareLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1CapFlat
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1CapFlat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1CapFlatLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
 (harg : (1:ℝ)-(z-p+((313/1000)-z+p))≠0) : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z harg] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1CapFlat


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadZero
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadZero
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadZeroLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadZero


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadCapBoundary
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper1HeadCapBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper1HeadCapBoundaryLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper1HeadCapBoundary


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedLower0HeadSquare
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedLower0HeadSquare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedLower0HeadSquareLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedLower0HeadSquare
