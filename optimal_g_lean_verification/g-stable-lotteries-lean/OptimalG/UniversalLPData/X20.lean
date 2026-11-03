import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x20 : DualProposal where
  support := #[(335, (-5426987378407697 / 3051757812500000))]
  objective := [(139, 1), (61, (-12359290787 / 10000000000))]
  residual := #[(-754351245598669883 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (5099757657 / 2441406250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x20_sparseResidual : Terms := [(0, (-754351245598669883 / 610351562500000000)), (61, (5099757657 / 2441406250000000000)), (139, (-25401 / 305175781250000000000))]
def x20_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000))]
  weightedRows := #[[(61, 7543512455986698830000000000), (0, (-7543512455986698830000000000)), (139, (-6103515625000000508020000000))]]
  residual := [(0, (-7543512455986698830000000000)), (61, 12749394142500000000), (139, (-508020000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 798980944531311375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-44185979337), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1593650681433336375, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-75850865937), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x20_expansion : IntegerTerms := [(139, 6103515625000000000000000000), (61, (-7543512443237304687500000000)), (61, 7543512455986698830000000000), (0, (-7543512455986698830000000000)), (139, (-6103515625000000508020000000))]
theorem x20_indices_checked : 0 < x20_integer.scale ∧ (baseCount+20) ≤ literalRows.size ∧ ∀ i, x20.rowIndex i < (baseCount+20) := by decide +kernel
theorem x20_sign_checked : ∀ i, x20.multiplier i ≤ 0 := by decide +kernel
theorem x20_objective_checked : scaledTermsCheck x20_integer.scale 1 x20.objective x20_integer.objective = true := by decide +kernel
theorem x20_rows_checked : ∀ i : Fin x20.support.size, scaledTermsCheck x20_integer.scale (-x20.multiplier i) literalTerms[x20.rowIndex i]! x20_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x20_expansion_checked : x20_integer.expanded x20 = x20_expansion := by decide +kernel
theorem x20_residual_checked : ∀ j : Variables, scaledIntegerCheck x20_integer.scale (x20.remainder j) (integerCoeff x20_integer.residual j) = true := by decide +kernel
theorem x20_rhs_checked : ∀ i : Fin x20.support.size, scaledProductCheck x20_integer.scale (x20.multiplier i) (x20.cachedRhs literalRhs i) x20_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x20_box_checked : ∀ j : Variables, scaledProductCheck x20_integer.scale (x20.remainder j) (lower j) x20_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x20_integer.scale (x20.remainder j) (upper j) x20_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x20_bound_checked : scaledIntegerCheck x20_integer.scale x20.bound x20_integer.bound = true := by decide +kernel
theorem x20_sum_checked : x20_integer.bound ≤ (∑ i : Fin x20.support.size, x20_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x20_integer.lowerProducts[j.val]! x20_integer.upperProducts[j.val]! := by decide +kernel
theorem x20_coeff00_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff01_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff02_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff03_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff04_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff05_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff06_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff07_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff08_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff09_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff10_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff11_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff12_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff13_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff14_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff15_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff16_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff17_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff18_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff19_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff20_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff21_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff22_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff23_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff24_checked : ∀ j : Fin 16, integerCoeff x20_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coeff25_checked : ∀ j : Fin 2, integerCoeff x20_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x20_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x20_coefficients_checked : ∀ j : Variables, integerCoeff x20_expansion j = integerCoeff x20_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x20_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x20_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x20_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x20_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x20_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x20_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x20_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x20_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x20_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x20_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x20_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x20_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x20_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x20_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x20_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x20_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x20_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x20_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x20_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x20_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x20_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x20_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x20_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x20_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x20_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x20_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x20_integer_checked : x20_integer.flatCoeffCheck x20 literalRows literalTerms literalRhs (baseCount+20) x20_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x20_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x20_indices_checked, x20_sign_checked⟩, x20_objective_checked⟩, x20_rows_checked⟩, x20_coefficients_checked⟩, x20_residual_checked⟩, x20_rhs_checked⟩, x20_box_checked⟩, x20_bound_checked⟩, x20_sum_checked⟩⟩
theorem x20_checked : x20.checkCached rows cachedTerms cachedRhs (baseCount+20) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x20_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x20_checked
end OptimalG.UniversalLP.Data
