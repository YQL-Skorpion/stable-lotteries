import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x61 : DualProposal where
  support := #[(343, (-5426987378407697 / 3051757812500000))]
  objective := [(144, 1), (56, (-12803869593 / 10000000000))]
  residual := #[(-48842886405669273 / 38146972656250000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5109317847 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x61_sparseResidual : Terms := [(0, (-48842886405669273 / 38146972656250000)), (56, (5109317847 / 2441406250000000000)), (144, (-25401 / 305175781250000000000))]
def x61_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000))]
  weightedRows := #[[(56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]]
  residual := [(0, (-976857728113385460000000000)), (56, 1596661827187500000), (144, (-63502500000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89289161364710250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-5292780969), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188809093053307125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9250891794), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x61_expansion : IntegerTerms := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000)), (56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]
theorem x61_indices_checked : 0 < x61_integer.scale ∧ (baseCount+61) ≤ literalRows.size ∧ ∀ i, x61.rowIndex i < (baseCount+61) := by decide +kernel
theorem x61_sign_checked : ∀ i, x61.multiplier i ≤ 0 := by decide +kernel
theorem x61_objective_checked : scaledTermsCheck x61_integer.scale 1 x61.objective x61_integer.objective = true := by decide +kernel
theorem x61_rows_checked : ∀ i : Fin x61.support.size, scaledTermsCheck x61_integer.scale (-x61.multiplier i) literalTerms[x61.rowIndex i]! x61_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x61_expansion_checked : x61_integer.expanded x61 = x61_expansion := by decide +kernel
theorem x61_residual_checked : ∀ j : Variables, scaledIntegerCheck x61_integer.scale (x61.remainder j) (integerCoeff x61_integer.residual j) = true := by decide +kernel
theorem x61_rhs_checked : ∀ i : Fin x61.support.size, scaledProductCheck x61_integer.scale (x61.multiplier i) (x61.cachedRhs literalRhs i) x61_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x61_box_checked : ∀ j : Variables, scaledProductCheck x61_integer.scale (x61.remainder j) (lower j) x61_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x61_integer.scale (x61.remainder j) (upper j) x61_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x61_bound_checked : scaledIntegerCheck x61_integer.scale x61.bound x61_integer.bound = true := by decide +kernel
theorem x61_sum_checked : x61_integer.bound ≤ (∑ i : Fin x61.support.size, x61_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x61_integer.lowerProducts[j.val]! x61_integer.upperProducts[j.val]! := by decide +kernel
theorem x61_coeff00_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff01_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff02_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff03_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff04_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff05_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff06_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff07_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff08_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff09_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff10_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff11_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff12_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff13_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff14_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff15_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff16_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff17_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff18_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff19_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff20_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff21_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff22_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff23_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff24_checked : ∀ j : Fin 16, integerCoeff x61_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coeff25_checked : ∀ j : Fin 2, integerCoeff x61_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x61_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x61_coefficients_checked : ∀ j : Variables, integerCoeff x61_expansion j = integerCoeff x61_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x61_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x61_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x61_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x61_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x61_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x61_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x61_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x61_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x61_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x61_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x61_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x61_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x61_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x61_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x61_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x61_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x61_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x61_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x61_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x61_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x61_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x61_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x61_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x61_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x61_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x61_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x61_integer_checked : x61_integer.flatCoeffCheck x61 literalRows literalTerms literalRhs (baseCount+61) x61_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x61_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x61_indices_checked, x61_sign_checked⟩, x61_objective_checked⟩, x61_rows_checked⟩, x61_coefficients_checked⟩, x61_residual_checked⟩, x61_rhs_checked⟩, x61_box_checked⟩, x61_bound_checked⟩, x61_sum_checked⟩⟩
theorem x61_checked : x61.checkCached rows cachedTerms cachedRhs (baseCount+61) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x61_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x61_checked
end OptimalG.UniversalLP.Data
