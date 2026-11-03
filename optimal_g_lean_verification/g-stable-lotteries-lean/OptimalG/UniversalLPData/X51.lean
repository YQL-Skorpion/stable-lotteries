import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x51 : DualProposal where
  support := #[(334, (-5426987378407697 / 3051757812500000))]
  objective := [(138, 1), (62, (-6135187513 / 5000000000))]
  residual := #[(-374462129110131093 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (2524508747 / 1220703125000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x51_sparseResidual : Terms := [(0, (-374462129110131093 / 305175781250000000)), (62, (2524508747 / 1220703125000000000)), (138, (-25401 / 305175781250000000000))]
def x51_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(138, 3051757812500000000000000000), (62, (-3744621284790039062500000000))]
  weightedRows := #[[(62, 3744621291101310930000000000), (0, (-3744621291101310930000000000)), (138, (-3051757812500000254010000000))]]
  residual := [(0, (-3744621291101310930000000000)), (62, 6311271867500000000), (138, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 403557239133245250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-22258312077), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 796938814634520250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-38090755377), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x51_expansion : IntegerTerms := [(138, 3051757812500000000000000000), (62, (-3744621284790039062500000000)), (62, 3744621291101310930000000000), (0, (-3744621291101310930000000000)), (138, (-3051757812500000254010000000))]
theorem x51_indices_checked : 0 < x51_integer.scale ∧ (baseCount+51) ≤ literalRows.size ∧ ∀ i, x51.rowIndex i < (baseCount+51) := by decide +kernel
theorem x51_sign_checked : ∀ i, x51.multiplier i ≤ 0 := by decide +kernel
theorem x51_objective_checked : scaledTermsCheck x51_integer.scale 1 x51.objective x51_integer.objective = true := by decide +kernel
theorem x51_rows_checked : ∀ i : Fin x51.support.size, scaledTermsCheck x51_integer.scale (-x51.multiplier i) literalTerms[x51.rowIndex i]! x51_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x51_expansion_checked : x51_integer.expanded x51 = x51_expansion := by decide +kernel
theorem x51_residual_checked : ∀ j : Variables, scaledIntegerCheck x51_integer.scale (x51.remainder j) (integerCoeff x51_integer.residual j) = true := by decide +kernel
theorem x51_rhs_checked : ∀ i : Fin x51.support.size, scaledProductCheck x51_integer.scale (x51.multiplier i) (x51.cachedRhs literalRhs i) x51_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x51_box_checked : ∀ j : Variables, scaledProductCheck x51_integer.scale (x51.remainder j) (lower j) x51_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x51_integer.scale (x51.remainder j) (upper j) x51_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x51_bound_checked : scaledIntegerCheck x51_integer.scale x51.bound x51_integer.bound = true := by decide +kernel
theorem x51_sum_checked : x51_integer.bound ≤ (∑ i : Fin x51.support.size, x51_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x51_integer.lowerProducts[j.val]! x51_integer.upperProducts[j.val]! := by decide +kernel
theorem x51_coeff00_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff01_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff02_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff03_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff04_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff05_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff06_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff07_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff08_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff09_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff10_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff11_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff12_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff13_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff14_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff15_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff16_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff17_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff18_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff19_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff20_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff21_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff22_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff23_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff24_checked : ∀ j : Fin 16, integerCoeff x51_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coeff25_checked : ∀ j : Fin 2, integerCoeff x51_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x51_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x51_coefficients_checked : ∀ j : Variables, integerCoeff x51_expansion j = integerCoeff x51_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x51_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x51_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x51_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x51_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x51_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x51_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x51_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x51_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x51_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x51_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x51_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x51_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x51_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x51_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x51_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x51_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x51_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x51_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x51_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x51_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x51_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x51_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x51_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x51_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x51_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x51_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x51_integer_checked : x51_integer.flatCoeffCheck x51 literalRows literalTerms literalRhs (baseCount+51) x51_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x51_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x51_indices_checked, x51_sign_checked⟩, x51_objective_checked⟩, x51_rows_checked⟩, x51_coefficients_checked⟩, x51_residual_checked⟩, x51_rhs_checked⟩, x51_box_checked⟩, x51_bound_checked⟩, x51_sum_checked⟩⟩
theorem x51_checked : x51.checkCached rows cachedTerms cachedRhs (baseCount+51) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x51_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x51_checked
end OptimalG.UniversalLP.Data
