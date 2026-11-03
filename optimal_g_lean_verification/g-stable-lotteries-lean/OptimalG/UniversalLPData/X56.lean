import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x56 : DualProposal where
  support := #[(341, (-5426987378407697 / 3051757812500000))]
  objective := [(142, 1), (58, (-12626038071 / 10000000000))]
  residual := #[(-385316103866946487 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5007837521 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x56_sparseResidual : Terms := [(0, (-385316103866946487 / 305175781250000000)), (58, (5007837521 / 2441406250000000000)), (142, (-25401 / 305175781250000000000))]
def x56_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000))]
  weightedRows := #[[(58, 3853161038669464870000000000), (0, (-3853161038669464870000000000)), (142, (-3051757812500000254010000000))]]
  residual := [(0, (-3853161038669464870000000000)), (58, 6259796901250000000), (142, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 367423160976699625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-21558920943), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 757596301831612125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-37391364243), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x56_expansion : IntegerTerms := [(142, 3051757812500000000000000000), (58, (-3853161032409667968750000000)), (58, 3853161038669464870000000000), (0, (-3853161038669464870000000000)), (142, (-3051757812500000254010000000))]
theorem x56_indices_checked : 0 < x56_integer.scale ∧ (baseCount+56) ≤ literalRows.size ∧ ∀ i, x56.rowIndex i < (baseCount+56) := by decide +kernel
theorem x56_sign_checked : ∀ i, x56.multiplier i ≤ 0 := by decide +kernel
theorem x56_objective_checked : scaledTermsCheck x56_integer.scale 1 x56.objective x56_integer.objective = true := by decide +kernel
theorem x56_rows_checked : ∀ i : Fin x56.support.size, scaledTermsCheck x56_integer.scale (-x56.multiplier i) literalTerms[x56.rowIndex i]! x56_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x56_expansion_checked : x56_integer.expanded x56 = x56_expansion := by decide +kernel
theorem x56_residual_checked : ∀ j : Variables, scaledIntegerCheck x56_integer.scale (x56.remainder j) (integerCoeff x56_integer.residual j) = true := by decide +kernel
theorem x56_rhs_checked : ∀ i : Fin x56.support.size, scaledProductCheck x56_integer.scale (x56.multiplier i) (x56.cachedRhs literalRhs i) x56_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x56_box_checked : ∀ j : Variables, scaledProductCheck x56_integer.scale (x56.remainder j) (lower j) x56_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x56_integer.scale (x56.remainder j) (upper j) x56_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x56_bound_checked : scaledIntegerCheck x56_integer.scale x56.bound x56_integer.bound = true := by decide +kernel
theorem x56_sum_checked : x56_integer.bound ≤ (∑ i : Fin x56.support.size, x56_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x56_integer.lowerProducts[j.val]! x56_integer.upperProducts[j.val]! := by decide +kernel
theorem x56_coeff00_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff01_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff02_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff03_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff04_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff05_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff06_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff07_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff08_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff09_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff10_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff11_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff12_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff13_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff14_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff15_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff16_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff17_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff18_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff19_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff20_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff21_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff22_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff23_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff24_checked : ∀ j : Fin 16, integerCoeff x56_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coeff25_checked : ∀ j : Fin 2, integerCoeff x56_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x56_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x56_coefficients_checked : ∀ j : Variables, integerCoeff x56_expansion j = integerCoeff x56_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x56_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x56_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x56_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x56_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x56_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x56_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x56_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x56_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x56_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x56_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x56_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x56_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x56_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x56_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x56_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x56_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x56_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x56_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x56_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x56_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x56_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x56_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x56_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x56_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x56_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x56_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x56_integer_checked : x56_integer.flatCoeffCheck x56 literalRows literalTerms literalRhs (baseCount+56) x56_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x56_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x56_indices_checked, x56_sign_checked⟩, x56_objective_checked⟩, x56_rows_checked⟩, x56_coefficients_checked⟩, x56_residual_checked⟩, x56_rhs_checked⟩, x56_box_checked⟩, x56_bound_checked⟩, x56_sum_checked⟩⟩
theorem x56_checked : x56.checkCached rows cachedTerms cachedRhs (baseCount+56) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x56_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x56_checked
end OptimalG.UniversalLP.Data
