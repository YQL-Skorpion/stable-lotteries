import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x60 : DualProposal where
  support := #[(343, (-5426987378407697 / 3051757812500000))]
  objective := [(144, 1), (56, (-12803869593 / 10000000000))]
  residual := #[(-48842886405669273 / 38146972656250000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5109317847 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x60_sparseResidual : Terms := [(0, (-48842886405669273 / 38146972656250000)), (56, (5109317847 / 2441406250000000000)), (144, (-25401 / 305175781250000000000))]
def x60_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000))]
  weightedRows := #[[(56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]]
  residual := [(0, (-976857728113385460000000000)), (56, 1596661827187500000), (144, (-63502500000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89289161364710250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-5292780969), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188809093053307125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-9250891794), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x60_expansion : IntegerTerms := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000)), (56, 976857728113385460000000000), (0, (-976857728113385460000000000)), (144, (-762939453125000063502500000))]
theorem x60_indices_checked : 0 < x60_integer.scale ∧ (baseCount+60) ≤ literalRows.size ∧ ∀ i, x60.rowIndex i < (baseCount+60) := by decide +kernel
theorem x60_sign_checked : ∀ i, x60.multiplier i ≤ 0 := by decide +kernel
theorem x60_objective_checked : scaledTermsCheck x60_integer.scale 1 x60.objective x60_integer.objective = true := by decide +kernel
theorem x60_rows_checked : ∀ i : Fin x60.support.size, scaledTermsCheck x60_integer.scale (-x60.multiplier i) literalTerms[x60.rowIndex i]! x60_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x60_expansion_checked : x60_integer.expanded x60 = x60_expansion := by decide +kernel
theorem x60_residual_checked : ∀ j : Variables, scaledIntegerCheck x60_integer.scale (x60.remainder j) (integerCoeff x60_integer.residual j) = true := by decide +kernel
theorem x60_rhs_checked : ∀ i : Fin x60.support.size, scaledProductCheck x60_integer.scale (x60.multiplier i) (x60.cachedRhs literalRhs i) x60_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x60_box_checked : ∀ j : Variables, scaledProductCheck x60_integer.scale (x60.remainder j) (lower j) x60_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x60_integer.scale (x60.remainder j) (upper j) x60_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x60_bound_checked : scaledIntegerCheck x60_integer.scale x60.bound x60_integer.bound = true := by decide +kernel
theorem x60_sum_checked : x60_integer.bound ≤ (∑ i : Fin x60.support.size, x60_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x60_integer.lowerProducts[j.val]! x60_integer.upperProducts[j.val]! := by decide +kernel
theorem x60_coeff00_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff01_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff02_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff03_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff04_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff05_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff06_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff07_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff08_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff09_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff10_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff11_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff12_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff13_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff14_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff15_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff16_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff17_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff18_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff19_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff20_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff21_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff22_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff23_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff24_checked : ∀ j : Fin 16, integerCoeff x60_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coeff25_checked : ∀ j : Fin 2, integerCoeff x60_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x60_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x60_coefficients_checked : ∀ j : Variables, integerCoeff x60_expansion j = integerCoeff x60_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x60_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x60_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x60_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x60_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x60_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x60_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x60_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x60_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x60_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x60_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x60_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x60_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x60_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x60_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x60_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x60_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x60_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x60_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x60_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x60_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x60_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x60_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x60_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x60_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x60_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x60_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x60_integer_checked : x60_integer.flatCoeffCheck x60 literalRows literalTerms literalRhs (baseCount+60) x60_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x60_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x60_indices_checked, x60_sign_checked⟩, x60_objective_checked⟩, x60_rows_checked⟩, x60_coefficients_checked⟩, x60_residual_checked⟩, x60_rhs_checked⟩, x60_box_checked⟩, x60_bound_checked⟩, x60_sum_checked⟩⟩
theorem x60_checked : x60.checkCached rows cachedTerms cachedRhs (baseCount+60) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x60_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x60_checked
end OptimalG.UniversalLP.Data
