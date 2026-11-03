import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch00


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1CapZeroTriangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapZeroTriangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapZeroTriangleLeaf000
theorem bound {p u : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (657/1000) (1413/2000))
    (hu : u∈Icc 0 1)
 (harg : (1:ℝ)-((p+(527/2000)+u*((97/100)-p-(527/2000)))-p+0)≠0) : target p u≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hu hzero
  have hd := denominator_pos hlam hS hp hu hzero
  rw [identity p u harg] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1CapZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadSquare
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadSquare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadSquareLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0CapFlat
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0CapFlat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0CapFlatLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0CapFlat


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadZero
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadZero
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadZeroLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadZero


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadCapBoundary
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.CurvedUpper0HeadCapBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.CurvedUpper0HeadCapBoundaryLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.CurvedUpper0HeadCapBoundary
