import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x65 : DualProposal where
  support := #[(347, (-339186711150481 / 190734863281250))]
  objective := [(146, 1), (54, (-3245425279 / 2500000000))]
  residual := #[(-24760629913985113 / 19073486328125000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1241664241 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1927 / 19073486328125000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x65_sparseResidual : Terms := [(0, (-24760629913985113 / 19073486328125000)), (54, (1241664241 / 610351562500000000)), (146, (1927 / 19073486328125000000))]
def x65_integer : IntegerDualCertificate where
  scale := 762939453125000000000000000
  objective := [(146, 762939453125000000000000000), (54, (-990425195007324218750000000))]
  weightedRows := #[[(54, 990425196559404520000000000), (0, (-990425196559404520000000000)), (146, (-762939453124999922920000000))]]
  residual := [(0, (-990425196559404520000000000)), (54, 1552080301250000000), (146, 77080000000)]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 82336463109041375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6299046972, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 179077628285953875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11103443372, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x65_expansion : IntegerTerms := [(146, 762939453125000000000000000), (54, (-990425195007324218750000000)), (54, 990425196559404520000000000), (0, (-990425196559404520000000000)), (146, (-762939453124999922920000000))]
theorem x65_indices_checked : 0 < x65_integer.scale ∧ (baseCount+65) ≤ literalRows.size ∧ ∀ i, x65.rowIndex i < (baseCount+65) := by decide +kernel
theorem x65_sign_checked : ∀ i, x65.multiplier i ≤ 0 := by decide +kernel
theorem x65_objective_checked : scaledTermsCheck x65_integer.scale 1 x65.objective x65_integer.objective = true := by decide +kernel
theorem x65_rows_checked : ∀ i : Fin x65.support.size, scaledTermsCheck x65_integer.scale (-x65.multiplier i) literalTerms[x65.rowIndex i]! x65_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x65_expansion_checked : x65_integer.expanded x65 = x65_expansion := by decide +kernel
theorem x65_residual_checked : ∀ j : Variables, scaledIntegerCheck x65_integer.scale (x65.remainder j) (integerCoeff x65_integer.residual j) = true := by decide +kernel
theorem x65_rhs_checked : ∀ i : Fin x65.support.size, scaledProductCheck x65_integer.scale (x65.multiplier i) (x65.cachedRhs literalRhs i) x65_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x65_box_checked : ∀ j : Variables, scaledProductCheck x65_integer.scale (x65.remainder j) (lower j) x65_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x65_integer.scale (x65.remainder j) (upper j) x65_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x65_bound_checked : scaledIntegerCheck x65_integer.scale x65.bound x65_integer.bound = true := by decide +kernel
theorem x65_sum_checked : x65_integer.bound ≤ (∑ i : Fin x65.support.size, x65_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x65_integer.lowerProducts[j.val]! x65_integer.upperProducts[j.val]! := by decide +kernel
theorem x65_coeff00_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff01_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff02_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff03_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff04_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff05_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff06_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff07_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff08_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff09_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff10_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff11_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff12_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff13_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff14_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff15_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff16_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff17_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff18_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff19_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff20_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff21_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff22_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff23_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff24_checked : ∀ j : Fin 16, integerCoeff x65_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coeff25_checked : ∀ j : Fin 2, integerCoeff x65_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x65_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x65_coefficients_checked : ∀ j : Variables, integerCoeff x65_expansion j = integerCoeff x65_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x65_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x65_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x65_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x65_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x65_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x65_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x65_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x65_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x65_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x65_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x65_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x65_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x65_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x65_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x65_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x65_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x65_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x65_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x65_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x65_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x65_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x65_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x65_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x65_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x65_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x65_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x65_integer_checked : x65_integer.flatCoeffCheck x65 literalRows literalTerms literalRhs (baseCount+65) x65_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x65_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x65_indices_checked, x65_sign_checked⟩, x65_objective_checked⟩, x65_rows_checked⟩, x65_coefficients_checked⟩, x65_residual_checked⟩, x65_rhs_checked⟩, x65_box_checked⟩, x65_bound_checked⟩, x65_sum_checked⟩⟩
theorem x65_checked : x65.checkCached rows cachedTerms cachedRhs (baseCount+65) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x65_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x65_checked
end OptimalG.UniversalLP.Data
