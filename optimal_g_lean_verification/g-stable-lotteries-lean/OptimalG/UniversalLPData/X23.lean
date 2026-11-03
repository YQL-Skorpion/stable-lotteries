import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x23 : DualProposal where
  support := #[(341, (-339186711150481 / 190734863281250))]
  objective := [(142, 1), (58, (-12626038071 / 10000000000))]
  residual := #[(-24082256491684151 / 19073486328125000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5007836953 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1927 / 19073486328125000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x23_sparseResidual : Terms := [(0, (-24082256491684151 / 19073486328125000)), (58, (5007836953 / 2441406250000000000)), (142, (1927 / 19073486328125000000))]
def x23_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000))]
  weightedRows := #[[(58, 3853161038669464160000000000), (0, (-3853161038669464160000000000)), (142, (-3051757812499999691680000000))]]
  residual := [(0, (-3853161038669464160000000000)), (58, 6259796191250000000), (142, 308320000000)]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 367423119302752625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26168444176, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 757596215903365125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45386029776, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x23_expansion : IntegerTerms := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000)), (58, 3853161038669464160000000000), (0, (-3853161038669464160000000000)), (142, (-3051757812499999691680000000))]
theorem x23_indices_checked : 0 < x23_integer.scale ∧ (baseCount+23) ≤ literalRows.size ∧ ∀ i, x23.rowIndex i < (baseCount+23) := by decide +kernel
theorem x23_sign_checked : ∀ i, x23.multiplier i ≤ 0 := by decide +kernel
theorem x23_objective_checked : scaledTermsCheck x23_integer.scale 1 x23.objective x23_integer.objective = true := by decide +kernel
theorem x23_rows_checked : ∀ i : Fin x23.support.size, scaledTermsCheck x23_integer.scale (-x23.multiplier i) literalTerms[x23.rowIndex i]! x23_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x23_expansion_checked : x23_integer.expanded x23 = x23_expansion := by decide +kernel
theorem x23_residual_checked : ∀ j : Variables, scaledIntegerCheck x23_integer.scale (x23.remainder j) (integerCoeff x23_integer.residual j) = true := by decide +kernel
theorem x23_rhs_checked : ∀ i : Fin x23.support.size, scaledProductCheck x23_integer.scale (x23.multiplier i) (x23.cachedRhs literalRhs i) x23_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x23_box_checked : ∀ j : Variables, scaledProductCheck x23_integer.scale (x23.remainder j) (lower j) x23_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x23_integer.scale (x23.remainder j) (upper j) x23_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x23_bound_checked : scaledIntegerCheck x23_integer.scale x23.bound x23_integer.bound = true := by decide +kernel
theorem x23_sum_checked : x23_integer.bound ≤ (∑ i : Fin x23.support.size, x23_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x23_integer.lowerProducts[j.val]! x23_integer.upperProducts[j.val]! := by decide +kernel
theorem x23_coeff00_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff01_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff02_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff03_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff04_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff05_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff06_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff07_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff08_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff09_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff10_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff11_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff12_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff13_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff14_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff15_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff16_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff17_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff18_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff19_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff20_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff21_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff22_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff23_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff24_checked : ∀ j : Fin 16, integerCoeff x23_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coeff25_checked : ∀ j : Fin 2, integerCoeff x23_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x23_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x23_coefficients_checked : ∀ j : Variables, integerCoeff x23_expansion j = integerCoeff x23_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x23_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x23_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x23_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x23_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x23_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x23_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x23_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x23_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x23_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x23_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x23_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x23_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x23_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x23_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x23_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x23_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x23_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x23_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x23_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x23_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x23_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x23_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x23_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x23_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x23_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x23_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x23_integer_checked : x23_integer.flatCoeffCheck x23 literalRows literalTerms literalRhs (baseCount+23) x23_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x23_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x23_indices_checked, x23_sign_checked⟩, x23_objective_checked⟩, x23_rows_checked⟩, x23_coefficients_checked⟩, x23_residual_checked⟩, x23_rhs_checked⟩, x23_box_checked⟩, x23_bound_checked⟩, x23_sum_checked⟩⟩
theorem x23_checked : x23.checkCached rows cachedTerms cachedRhs (baseCount+23) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x23_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x23_checked
end OptimalG.UniversalLP.Data
