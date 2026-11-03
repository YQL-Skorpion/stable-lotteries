import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x54 : DualProposal where
  support := #[(338, (-5426987378407697 / 3051757812500000))]
  objective := [(140, 1), (60, (-12448206549 / 10000000000))]
  residual := #[(-37988911648853879 / 30517578125000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (981271439 / 488281250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x54_sparseResidual : Terms := [(0, (-37988911648853879 / 30517578125000000)), (60, (981271439 / 488281250000000000)), (140, (-25401 / 305175781250000000000))]
def x54_integer : IntegerDualCertificate where
  scale := 305175781250000000000000000
  objective := [(140, 305175781250000000000000000), (60, (-379889115875244140625000000))]
  weightedRows := #[[(60, 379889116488538790000000000), (0, (-379889116488538790000000000)), (140, (-305175781250000025401000000))]]
  residual := [(0, (-379889116488538790000000000)), (60, 613294649375000000), (140, (-25401000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 37637279337494375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-2192131701), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 75863934833038125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-3775376031), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x54_expansion : IntegerTerms := [(140, 305175781250000000000000000), (60, (-379889115875244140625000000)), (60, 379889116488538790000000000), (0, (-379889116488538790000000000)), (140, (-305175781250000025401000000))]
theorem x54_indices_checked : 0 < x54_integer.scale ∧ (baseCount+54) ≤ literalRows.size ∧ ∀ i, x54.rowIndex i < (baseCount+54) := by decide +kernel
theorem x54_sign_checked : ∀ i, x54.multiplier i ≤ 0 := by decide +kernel
theorem x54_objective_checked : scaledTermsCheck x54_integer.scale 1 x54.objective x54_integer.objective = true := by decide +kernel
theorem x54_rows_checked : ∀ i : Fin x54.support.size, scaledTermsCheck x54_integer.scale (-x54.multiplier i) literalTerms[x54.rowIndex i]! x54_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x54_expansion_checked : x54_integer.expanded x54 = x54_expansion := by decide +kernel
theorem x54_residual_checked : ∀ j : Variables, scaledIntegerCheck x54_integer.scale (x54.remainder j) (integerCoeff x54_integer.residual j) = true := by decide +kernel
theorem x54_rhs_checked : ∀ i : Fin x54.support.size, scaledProductCheck x54_integer.scale (x54.multiplier i) (x54.cachedRhs literalRhs i) x54_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x54_box_checked : ∀ j : Variables, scaledProductCheck x54_integer.scale (x54.remainder j) (lower j) x54_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x54_integer.scale (x54.remainder j) (upper j) x54_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x54_bound_checked : scaledIntegerCheck x54_integer.scale x54.bound x54_integer.bound = true := by decide +kernel
theorem x54_sum_checked : x54_integer.bound ≤ (∑ i : Fin x54.support.size, x54_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x54_integer.lowerProducts[j.val]! x54_integer.upperProducts[j.val]! := by decide +kernel
theorem x54_coeff00_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff01_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff02_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff03_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff04_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff05_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff06_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff07_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff08_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff09_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff10_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff11_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff12_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff13_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff14_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff15_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff16_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff17_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff18_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff19_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff20_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff21_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff22_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff23_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff24_checked : ∀ j : Fin 16, integerCoeff x54_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coeff25_checked : ∀ j : Fin 2, integerCoeff x54_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x54_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x54_coefficients_checked : ∀ j : Variables, integerCoeff x54_expansion j = integerCoeff x54_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x54_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x54_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x54_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x54_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x54_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x54_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x54_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x54_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x54_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x54_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x54_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x54_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x54_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x54_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x54_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x54_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x54_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x54_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x54_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x54_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x54_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x54_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x54_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x54_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x54_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x54_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x54_integer_checked : x54_integer.flatCoeffCheck x54 literalRows literalTerms literalRhs (baseCount+54) x54_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x54_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x54_indices_checked, x54_sign_checked⟩, x54_objective_checked⟩, x54_rows_checked⟩, x54_coefficients_checked⟩, x54_residual_checked⟩, x54_rhs_checked⟩, x54_box_checked⟩, x54_bound_checked⟩, x54_sum_checked⟩⟩
theorem x54_checked : x54.checkCached rows cachedTerms cachedRhs (baseCount+54) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x54_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x54_checked
end OptimalG.UniversalLP.Data
