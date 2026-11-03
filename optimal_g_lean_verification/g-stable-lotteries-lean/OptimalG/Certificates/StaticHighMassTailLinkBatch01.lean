import OptimalG.Certificates.LargeTailExpressions
import OptimalG.Certificates.StaticHighMassTailDataBatch00


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryRectangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0HeadCapBoundaryRectangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0HeadCapBoundaryRectangleLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryRectangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapZeroRectangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroRectangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroRectangleLeaf000
theorem bound {p u : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (657/1000))
    (hu : u∈Icc 0 1)
 (harg : (1:ℝ)-((p+(527/2000)+u*((313/1000)-(527/2000)))-p+0)≠0) : target p u≤0 := by
  have hzero : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,by norm_num⟩
  have hn := numerator_pos hlam hS hp hu hzero
  have hd := denominator_pos hlam hS hp hu hzero
  rw [identity p u harg] at hn
  have hh := nonneg_of_mul_nonneg_left hn.le hd
  linarith only [hh]
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapZeroRectangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapZeroTriangle
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper0CapZeroTriangle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper0CapZeroTriangleLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper0CapZeroTriangle


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1HeadSquare
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1HeadSquare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1HeadSquareLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1HeadSquare


namespace OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1CapFlat
open Set LargeTailExpressions
open OptimalG.Certificates.StaticHighMassTailModels.Before97.LineUpper1CapFlat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open OptimalG.Certificates.StaticHighMassTailData.Before97.LineUpper1CapFlatLeaf000
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
end OptimalG.Certificates.StaticHighMassTailLinks.Before97.LineUpper1CapFlat
