import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x59 : DualProposal where
  support := #[(343, (-5426987378407697 / 3051757812500000))]
  objective := [(144, 1), (56, (-12803869593 / 10000000000))]
  residual := #[(-48842886405669273 / 38146972656250000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5109317847 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x59_sparseResidual : Terms := [(0, (-48842886405669273 / 38146972656250000)), (56, (5109317847 / 2441406250000000000)), (144, (-25401 / 305175781250000000000))]
def x59_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000))]
  weightedRows := #[[(56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]]
  residual := [(0, (-976857728113385460000000000)), (56, 1596661827187500000), (144, (-63502500000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89289161364710250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-5292780969), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188809093053307125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9250891794), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x59_expansion : IntegerTerms := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000)), (56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]
theorem x59_indices_checked : 0 < x59_integer.scale ∧ (baseCount+59) ≤ literalRows.size ∧ ∀ i, x59.rowIndex i < (baseCount+59) := by decide +kernel
theorem x59_sign_checked : ∀ i, x59.multiplier i ≤ 0 := by decide +kernel
theorem x59_objective_checked : scaledTermsCheck x59_integer.scale 1 x59.objective x59_integer.objective = true := by decide +kernel
theorem x59_rows_checked : ∀ i : Fin x59.support.size, scaledTermsCheck x59_integer.scale (-x59.multiplier i) literalTerms[x59.rowIndex i]! x59_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x59_expansion_checked : x59_integer.expanded x59 = x59_expansion := by decide +kernel
theorem x59_residual_checked : ∀ j : Variables, scaledIntegerCheck x59_integer.scale (x59.remainder j) (integerCoeff x59_integer.residual j) = true := by decide +kernel
theorem x59_rhs_checked : ∀ i : Fin x59.support.size, scaledProductCheck x59_integer.scale (x59.multiplier i) (x59.cachedRhs literalRhs i) x59_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x59_box_checked : ∀ j : Variables, scaledProductCheck x59_integer.scale (x59.remainder j) (lower j) x59_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x59_integer.scale (x59.remainder j) (upper j) x59_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x59_bound_checked : scaledIntegerCheck x59_integer.scale x59.bound x59_integer.bound = true := by decide +kernel
theorem x59_sum_checked : x59_integer.bound ≤ (∑ i : Fin x59.support.size, x59_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x59_integer.lowerProducts[j.val]! x59_integer.upperProducts[j.val]! := by decide +kernel
theorem x59_coeff00_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff01_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff02_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff03_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff04_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff05_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff06_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff07_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff08_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff09_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff10_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff11_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff12_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff13_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff14_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff15_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff16_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff17_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff18_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff19_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff20_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff21_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff22_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff23_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff24_checked : ∀ j : Fin 16, integerCoeff x59_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coeff25_checked : ∀ j : Fin 2, integerCoeff x59_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x59_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x59_coefficients_checked : ∀ j : Variables, integerCoeff x59_expansion j = integerCoeff x59_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x59_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x59_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x59_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x59_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x59_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x59_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x59_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x59_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x59_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x59_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x59_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x59_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x59_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x59_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x59_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x59_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x59_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x59_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x59_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x59_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x59_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x59_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x59_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x59_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x59_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x59_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x59_integer_checked : x59_integer.flatCoeffCheck x59 literalRows literalTerms literalRhs (baseCount+59) x59_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x59_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x59_indices_checked, x59_sign_checked⟩, x59_objective_checked⟩, x59_rows_checked⟩, x59_coefficients_checked⟩, x59_residual_checked⟩, x59_rhs_checked⟩, x59_box_checked⟩, x59_bound_checked⟩, x59_sum_checked⟩⟩
theorem x59_checked : x59.checkCached rows cachedTerms cachedRhs (baseCount+59) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x59_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x59_checked
end OptimalG.UniversalLP.Data
