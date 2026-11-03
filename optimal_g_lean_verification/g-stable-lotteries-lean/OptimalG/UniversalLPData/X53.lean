import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x53 : DualProposal where
  support := #[(335, (-339186711150481 / 190734863281250))]
  objective := [(139, 1), (61, (-12359290787 / 10000000000))]
  residual := #[(-47146952849916859 / 38146972656250000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5099757101 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1927 / 19073486328125000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x53_sparseResidual : Terms := [(0, (-47146952849916859 / 38146972656250000)), (61, (5099757101 / 2441406250000000000)), (139, (1927 / 19073486328125000000))]
def x53_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000))]
  weightedRows := #[[(61, 7543512455986697440000000000), (0, (-7543512455986697440000000000)), (139, (-6103515624999999383360000000))]]
  residual := [(0, (-7543512455986697440000000000)), (61, 12749392752500000000), (139, 616640000000)]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 798980857422582875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53633404784, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1593650507685907875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 92068575984, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x53_expansion : IntegerTerms := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000)), (61, 7543512455986697440000000000), (0, (-7543512455986697440000000000)), (139, (-6103515624999999383360000000))]
theorem x53_indices_checked : 0 < x53_integer.scale ∧ (baseCount+53) ≤ literalRows.size ∧ ∀ i, x53.rowIndex i < (baseCount+53) := by decide +kernel
theorem x53_sign_checked : ∀ i, x53.multiplier i ≤ 0 := by decide +kernel
theorem x53_objective_checked : scaledTermsCheck x53_integer.scale 1 x53.objective x53_integer.objective = true := by decide +kernel
theorem x53_rows_checked : ∀ i : Fin x53.support.size, scaledTermsCheck x53_integer.scale (-x53.multiplier i) literalTerms[x53.rowIndex i]! x53_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x53_expansion_checked : x53_integer.expanded x53 = x53_expansion := by decide +kernel
theorem x53_residual_checked : ∀ j : Variables, scaledIntegerCheck x53_integer.scale (x53.remainder j) (integerCoeff x53_integer.residual j) = true := by decide +kernel
theorem x53_rhs_checked : ∀ i : Fin x53.support.size, scaledProductCheck x53_integer.scale (x53.multiplier i) (x53.cachedRhs literalRhs i) x53_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x53_box_checked : ∀ j : Variables, scaledProductCheck x53_integer.scale (x53.remainder j) (lower j) x53_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x53_integer.scale (x53.remainder j) (upper j) x53_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x53_bound_checked : scaledIntegerCheck x53_integer.scale x53.bound x53_integer.bound = true := by decide +kernel
theorem x53_sum_checked : x53_integer.bound ≤ (∑ i : Fin x53.support.size, x53_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x53_integer.lowerProducts[j.val]! x53_integer.upperProducts[j.val]! := by decide +kernel
theorem x53_coeff00_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff01_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff02_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff03_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff04_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff05_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff06_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff07_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff08_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff09_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff10_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff11_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff12_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff13_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff14_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff15_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff16_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff17_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff18_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff19_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff20_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff21_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff22_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff23_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff24_checked : ∀ j : Fin 16, integerCoeff x53_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coeff25_checked : ∀ j : Fin 2, integerCoeff x53_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x53_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x53_coefficients_checked : ∀ j : Variables, integerCoeff x53_expansion j = integerCoeff x53_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x53_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x53_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x53_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x53_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x53_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x53_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x53_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x53_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x53_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x53_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x53_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x53_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x53_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x53_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x53_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x53_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x53_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x53_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x53_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x53_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x53_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x53_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x53_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x53_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x53_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x53_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x53_integer_checked : x53_integer.flatCoeffCheck x53 literalRows literalTerms literalRhs (baseCount+53) x53_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x53_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x53_indices_checked, x53_sign_checked⟩, x53_objective_checked⟩, x53_rows_checked⟩, x53_coefficients_checked⟩, x53_residual_checked⟩, x53_rhs_checked⟩, x53_box_checked⟩, x53_bound_checked⟩, x53_sum_checked⟩⟩
theorem x53_checked : x53.checkCached rows cachedTerms cachedRhs (baseCount+53) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x53_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x53_checked
end OptimalG.UniversalLP.Data
