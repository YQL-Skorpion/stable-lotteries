import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x27 : DualProposal where
  support := #[(343, (-5426987378407697 / 3051757812500000))]
  objective := [(144, 1), (56, (-12803869593 / 10000000000))]
  residual := #[(-48842886405669273 / 38146972656250000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5109317847 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x27_sparseResidual : Terms := [(0, (-48842886405669273 / 38146972656250000)), (56, (5109317847 / 2441406250000000000)), (144, (-25401 / 305175781250000000000))]
def x27_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000))]
  weightedRows := #[[(56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]]
  residual := [(0, (-976857728113385460000000000)), (56, 1596661827187500000), (144, (-63502500000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89289161364710250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-5292780969), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188809093053307125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9250891794), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x27_expansion : IntegerTerms := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000)), (56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]
theorem x27_indices_checked : 0 < x27_integer.scale ∧ (baseCount+27) ≤ literalRows.size ∧ ∀ i, x27.rowIndex i < (baseCount+27) := by decide +kernel
theorem x27_sign_checked : ∀ i, x27.multiplier i ≤ 0 := by decide +kernel
theorem x27_objective_checked : scaledTermsCheck x27_integer.scale 1 x27.objective x27_integer.objective = true := by decide +kernel
theorem x27_rows_checked : ∀ i : Fin x27.support.size, scaledTermsCheck x27_integer.scale (-x27.multiplier i) literalTerms[x27.rowIndex i]! x27_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x27_expansion_checked : x27_integer.expanded x27 = x27_expansion := by decide +kernel
theorem x27_residual_checked : ∀ j : Variables, scaledIntegerCheck x27_integer.scale (x27.remainder j) (integerCoeff x27_integer.residual j) = true := by decide +kernel
theorem x27_rhs_checked : ∀ i : Fin x27.support.size, scaledProductCheck x27_integer.scale (x27.multiplier i) (x27.cachedRhs literalRhs i) x27_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x27_box_checked : ∀ j : Variables, scaledProductCheck x27_integer.scale (x27.remainder j) (lower j) x27_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x27_integer.scale (x27.remainder j) (upper j) x27_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x27_bound_checked : scaledIntegerCheck x27_integer.scale x27.bound x27_integer.bound = true := by decide +kernel
theorem x27_sum_checked : x27_integer.bound ≤ (∑ i : Fin x27.support.size, x27_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x27_integer.lowerProducts[j.val]! x27_integer.upperProducts[j.val]! := by decide +kernel
theorem x27_coeff00_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff01_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff02_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff03_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff04_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff05_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff06_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff07_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff08_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff09_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff10_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff11_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff12_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff13_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff14_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff15_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff16_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff17_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff18_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff19_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff20_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff21_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff22_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff23_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff24_checked : ∀ j : Fin 16, integerCoeff x27_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coeff25_checked : ∀ j : Fin 2, integerCoeff x27_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x27_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x27_coefficients_checked : ∀ j : Variables, integerCoeff x27_expansion j = integerCoeff x27_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x27_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x27_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x27_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x27_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x27_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x27_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x27_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x27_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x27_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x27_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x27_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x27_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x27_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x27_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x27_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x27_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x27_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x27_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x27_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x27_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x27_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x27_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x27_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x27_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x27_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x27_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x27_integer_checked : x27_integer.flatCoeffCheck x27 literalRows literalTerms literalRhs (baseCount+27) x27_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x27_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x27_indices_checked, x27_sign_checked⟩, x27_objective_checked⟩, x27_rows_checked⟩, x27_coefficients_checked⟩, x27_residual_checked⟩, x27_rhs_checked⟩, x27_box_checked⟩, x27_bound_checked⟩, x27_sum_checked⟩⟩
theorem x27_checked : x27.checkCached rows cachedTerms cachedRhs (baseCount+27) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x27_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x27_checked
end OptimalG.UniversalLP.Data
