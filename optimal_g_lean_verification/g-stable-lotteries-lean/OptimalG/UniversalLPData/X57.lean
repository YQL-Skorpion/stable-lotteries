import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x57 : DualProposal where
  support := #[(341, (-5426987378407697 / 3051757812500000))]
  objective := [(142, 1), (58, (-12626038071 / 10000000000))]
  residual := #[(-385316103866946487 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5007837521 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x57_sparseResidual : Terms := [(0, (-385316103866946487 / 305175781250000000)), (58, (5007837521 / 2441406250000000000)), (142, (-25401 / 305175781250000000000))]
def x57_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000))]
  weightedRows := #[[(58, 3853161038669464870000000000), (0, (-3853161038669464870000000000)), (142, (-3051757812500000254010000000))]]
  residual := [(0, (-3853161038669464870000000000)), (58, 6259796901250000000), (142, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 367423160976699625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-21558920943), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 757596301831612125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-37391364243), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x57_expansion : IntegerTerms := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000)), (58, 3853161038669464870000000000), (0, (-3853161038669464870000000000)), (142, (-3051757812500000254010000000))]
theorem x57_indices_checked : 0 < x57_integer.scale ∧ (baseCount+57) ≤ literalRows.size ∧ ∀ i, x57.rowIndex i < (baseCount+57) := by decide +kernel
theorem x57_sign_checked : ∀ i, x57.multiplier i ≤ 0 := by decide +kernel
theorem x57_objective_checked : scaledTermsCheck x57_integer.scale 1 x57.objective x57_integer.objective = true := by decide +kernel
theorem x57_rows_checked : ∀ i : Fin x57.support.size, scaledTermsCheck x57_integer.scale (-x57.multiplier i) literalTerms[x57.rowIndex i]! x57_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x57_expansion_checked : x57_integer.expanded x57 = x57_expansion := by decide +kernel
theorem x57_residual_checked : ∀ j : Variables, scaledIntegerCheck x57_integer.scale (x57.remainder j) (integerCoeff x57_integer.residual j) = true := by decide +kernel
theorem x57_rhs_checked : ∀ i : Fin x57.support.size, scaledProductCheck x57_integer.scale (x57.multiplier i) (x57.cachedRhs literalRhs i) x57_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x57_box_checked : ∀ j : Variables, scaledProductCheck x57_integer.scale (x57.remainder j) (lower j) x57_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x57_integer.scale (x57.remainder j) (upper j) x57_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x57_bound_checked : scaledIntegerCheck x57_integer.scale x57.bound x57_integer.bound = true := by decide +kernel
theorem x57_sum_checked : x57_integer.bound ≤ (∑ i : Fin x57.support.size, x57_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x57_integer.lowerProducts[j.val]! x57_integer.upperProducts[j.val]! := by decide +kernel
theorem x57_coeff00_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff01_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff02_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff03_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff04_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff05_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff06_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff07_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff08_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff09_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff10_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff11_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff12_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff13_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff14_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff15_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff16_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff17_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff18_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff19_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff20_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff21_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff22_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff23_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff24_checked : ∀ j : Fin 16, integerCoeff x57_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coeff25_checked : ∀ j : Fin 2, integerCoeff x57_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x57_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x57_coefficients_checked : ∀ j : Variables, integerCoeff x57_expansion j = integerCoeff x57_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x57_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x57_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x57_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x57_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x57_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x57_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x57_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x57_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x57_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x57_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x57_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x57_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x57_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x57_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x57_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x57_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x57_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x57_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x57_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x57_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x57_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x57_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x57_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x57_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x57_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x57_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x57_integer_checked : x57_integer.flatCoeffCheck x57 literalRows literalTerms literalRhs (baseCount+57) x57_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x57_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x57_indices_checked, x57_sign_checked⟩, x57_objective_checked⟩, x57_rows_checked⟩, x57_coefficients_checked⟩, x57_residual_checked⟩, x57_rhs_checked⟩, x57_box_checked⟩, x57_bound_checked⟩, x57_sum_checked⟩⟩
theorem x57_checked : x57.checkCached rows cachedTerms cachedRhs (baseCount+57) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x57_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x57_checked
end OptimalG.UniversalLP.Data
