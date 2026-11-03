import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x19 : DualProposal where
  support := #[(335, (-5426987378407697 / 3051757812500000))]
  objective := [(139, 1), (61, (-12359290787 / 10000000000))]
  residual := #[(-754351245598669883 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5099757657 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x19_sparseResidual : Terms := [(0, (-754351245598669883 / 610351562500000000)), (61, (5099757657 / 2441406250000000000)), (139, (-25401 / 305175781250000000000))]
def x19_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000))]
  weightedRows := #[[(61, 7543512455986698830000000000), (0, (-7543512455986698830000000000)), (139, (-6103515625000000508020000000))]]
  residual := [(0, (-7543512455986698830000000000)), (61, 12749394142500000000), (139, (-508020000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 798980944531311375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-44185979337), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1593650681433336375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-75850865937), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x19_expansion : IntegerTerms := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000)), (61, 7543512455986698830000000000), (0, (-7543512455986698830000000000)), (139, (-6103515625000000508020000000))]
theorem x19_indices_checked : 0 < x19_integer.scale ∧ (baseCount+19) ≤ literalRows.size ∧ ∀ i, x19.rowIndex i < (baseCount+19) := by decide +kernel
theorem x19_sign_checked : ∀ i, x19.multiplier i ≤ 0 := by decide +kernel
theorem x19_objective_checked : scaledTermsCheck x19_integer.scale 1 x19.objective x19_integer.objective = true := by decide +kernel
theorem x19_rows_checked : ∀ i : Fin x19.support.size, scaledTermsCheck x19_integer.scale (-x19.multiplier i) literalTerms[x19.rowIndex i]! x19_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x19_expansion_checked : x19_integer.expanded x19 = x19_expansion := by decide +kernel
theorem x19_residual_checked : ∀ j : Variables, scaledIntegerCheck x19_integer.scale (x19.remainder j) (integerCoeff x19_integer.residual j) = true := by decide +kernel
theorem x19_rhs_checked : ∀ i : Fin x19.support.size, scaledProductCheck x19_integer.scale (x19.multiplier i) (x19.cachedRhs literalRhs i) x19_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x19_box_checked : ∀ j : Variables, scaledProductCheck x19_integer.scale (x19.remainder j) (lower j) x19_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x19_integer.scale (x19.remainder j) (upper j) x19_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x19_bound_checked : scaledIntegerCheck x19_integer.scale x19.bound x19_integer.bound = true := by decide +kernel
theorem x19_sum_checked : x19_integer.bound ≤ (∑ i : Fin x19.support.size, x19_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x19_integer.lowerProducts[j.val]! x19_integer.upperProducts[j.val]! := by decide +kernel
theorem x19_coeff00_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff01_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff02_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff03_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff04_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff05_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff06_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff07_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff08_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff09_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff10_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff11_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff12_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff13_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff14_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff15_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff16_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff17_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff18_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff19_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff20_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff21_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff22_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff23_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff24_checked : ∀ j : Fin 16, integerCoeff x19_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coeff25_checked : ∀ j : Fin 2, integerCoeff x19_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x19_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x19_coefficients_checked : ∀ j : Variables, integerCoeff x19_expansion j = integerCoeff x19_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x19_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x19_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x19_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x19_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x19_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x19_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x19_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x19_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x19_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x19_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x19_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x19_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x19_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x19_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x19_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x19_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x19_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x19_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x19_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x19_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x19_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x19_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x19_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x19_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x19_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x19_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x19_integer_checked : x19_integer.flatCoeffCheck x19 literalRows literalTerms literalRhs (baseCount+19) x19_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x19_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x19_indices_checked, x19_sign_checked⟩, x19_objective_checked⟩, x19_rows_checked⟩, x19_coefficients_checked⟩, x19_residual_checked⟩, x19_rhs_checked⟩, x19_box_checked⟩, x19_bound_checked⟩, x19_sum_checked⟩⟩
theorem x19_checked : x19.checkCached rows cachedTerms cachedRhs (baseCount+19) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x19_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x19_checked
end OptimalG.UniversalLP.Data
