import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch00


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadSquare
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadSquare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadSquareLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapFlat
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapFlat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapFlatLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (7/8) (97/100))
 (harg : (1:ℝ)-(z-p+((313/1000)-z+p))≠0) : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z harg] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapFlat


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadZeroTriangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroTriangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroTriangleLeaf000
theorem bound {p u : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
 : target p u≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hu hzero
  have hd := denominator_pos hlam hS hp hu hzero
  rw [identity p u] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadZeroRectangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadZeroRectangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadZeroRectangleLeaf000
theorem bound {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (1413/2000) (391/500))
    (hz : z∈Icc (7/8) (97/100))
 : target p z≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hz hzero
  have hd := denominator_pos hlam hS hp hz hzero
  rw [identity p z] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadZeroRectangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryTriangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryTriangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryTriangleLeaf000
theorem bound {p u : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (1413/2000))
    (hu : u∈Icc 0 1)
 : target p u≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hu hzero
  have hd := denominator_pos hlam hS hp hu hzero
  rw [identity p u] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryTriangle
