import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x26 : DualProposal where
  support := #[(343, (-339186711150481 / 190734863281250))]
  objective := [(144, 1), (56, (-12803869593 / 10000000000))]
  residual := #[(-3052680400354329 / 2384185791015625), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5109317271 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1927 / 19073486328125000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x26_sparseResidual : Terms := [(0, (-3052680400354329 / 2384185791015625)), (56, (5109317271 / 2441406250000000000)), (144, (1927 / 19073486328125000000))]
def x26_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000))]
  weightedRows := #[[(56, 976857728113385280000000000), (0, (-976857728113385280000000000)), (144, (-762939453124999922920000000))]]
  residual := [(0, (-976857728113385280000000000)), (56, 1596661647187500000), (144, 77080000000)]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89289151298678250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6424433008, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 188809071767875125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11228829408, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x26_expansion : IntegerTerms := [(144, 762939453125000000000000000), (56, (-976857726516723632812500000)), (56, 976857728113385280000000000), (0, (-976857728113385280000000000)), (144, (-762939453124999922920000000))]
theorem x26_indices_checked : 0 < x26_integer.scale ∧ (baseCount+26) ≤ literalRows.size ∧ ∀ i, x26.rowIndex i < (baseCount+26) := by decide +kernel
theorem x26_sign_checked : ∀ i, x26.multiplier i ≤ 0 := by decide +kernel
theorem x26_objective_checked : scaledTermsCheck x26_integer.scale 1 x26.objective x26_integer.objective = true := by decide +kernel
theorem x26_rows_checked : ∀ i : Fin x26.support.size, scaledTermsCheck x26_integer.scale (-x26.multiplier i) literalTerms[x26.rowIndex i]! x26_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x26_expansion_checked : x26_integer.expanded x26 = x26_expansion := by decide +kernel
theorem x26_residual_checked : ∀ j : Variables, scaledIntegerCheck x26_integer.scale (x26.remainder j) (integerCoeff x26_integer.residual j) = true := by decide +kernel
theorem x26_rhs_checked : ∀ i : Fin x26.support.size, scaledProductCheck x26_integer.scale (x26.multiplier i) (x26.cachedRhs literalRhs i) x26_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x26_box_checked : ∀ j : Variables, scaledProductCheck x26_integer.scale (x26.remainder j) (lower j) x26_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x26_integer.scale (x26.remainder j) (upper j) x26_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x26_bound_checked : scaledIntegerCheck x26_integer.scale x26.bound x26_integer.bound = true := by decide +kernel
theorem x26_sum_checked : x26_integer.bound ≤ (∑ i : Fin x26.support.size, x26_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x26_integer.lowerProducts[j.val]! x26_integer.upperProducts[j.val]! := by decide +kernel
theorem x26_coeff00_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff01_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff02_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff03_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff04_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff05_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff06_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff07_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff08_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff09_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff10_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff11_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff12_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff13_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff14_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff15_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff16_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff17_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff18_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff19_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff20_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff21_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff22_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff23_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff24_checked : ∀ j : Fin 16, integerCoeff x26_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coeff25_checked : ∀ j : Fin 2, integerCoeff x26_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x26_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x26_coefficients_checked : ∀ j : Variables, integerCoeff x26_expansion j = integerCoeff x26_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x26_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x26_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x26_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x26_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x26_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x26_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x26_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x26_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x26_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x26_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x26_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x26_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x26_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x26_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x26_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x26_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x26_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x26_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x26_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x26_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x26_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x26_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x26_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x26_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x26_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x26_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x26_integer_checked : x26_integer.flatCoeffCheck x26 literalRows literalTerms literalRhs (baseCount+26) x26_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x26_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x26_indices_checked, x26_sign_checked⟩, x26_objective_checked⟩, x26_rows_checked⟩, x26_coefficients_checked⟩, x26_residual_checked⟩, x26_rhs_checked⟩, x26_box_checked⟩, x26_bound_checked⟩, x26_sum_checked⟩⟩
theorem x26_checked : x26.checkCached rows cachedTerms cachedRhs (baseCount+26) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x26_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x26_checked
end OptimalG.UniversalLP.Data
