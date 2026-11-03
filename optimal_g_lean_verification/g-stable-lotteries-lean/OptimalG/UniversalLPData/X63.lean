import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x63 : DualProposal where
  support := #[(345, (-1085397475681539 / 610351562500000))]
  objective := [(145, 1), (55, (-2578557071 / 2000000000))]
  residual := #[(-31476526794764631 / 24414062500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (196636649 / 97656250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (17413 / 61035156250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x63_sparseResidual : Terms := [(0, (-31476526794764631 / 24414062500000000)), (55, (196636649 / 97656250000000000)), (145, (17413 / 61035156250000000000))]
def x63_integer : IntegerDualCertificate where
  scale := 244140625000000000000000000
  objective := [(145, 244140625000000000000000000), (55, (-314765267456054687500000000))]
  weightedRows := #[[(55, 314765267947646310000000000), (0, (-314765267947646310000000000)), (145, (-244140624999999930348000000))]]
  residual := [(0, (-314765267947646310000000000)), (55, 491591622500000000), (145, 69652000000)]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26790883140910625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5749546231, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57431788971335625, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10090955391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x63_expansion : IntegerTerms := [(145, 244140625000000000000000000), (55, (-314765267456054687500000000)), (55, 314765267947646310000000000), (0, (-314765267947646310000000000)), (145, (-244140624999999930348000000))]
theorem x63_indices_checked : 0 < x63_integer.scale ∧ (baseCount+63) ≤ literalRows.size ∧ ∀ i, x63.rowIndex i < (baseCount+63) := by decide +kernel
theorem x63_sign_checked : ∀ i, x63.multiplier i ≤ 0 := by decide +kernel
theorem x63_objective_checked : scaledTermsCheck x63_integer.scale 1 x63.objective x63_integer.objective = true := by decide +kernel
theorem x63_rows_checked : ∀ i : Fin x63.support.size, scaledTermsCheck x63_integer.scale (-x63.multiplier i) literalTerms[x63.rowIndex i]! x63_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x63_expansion_checked : x63_integer.expanded x63 = x63_expansion := by decide +kernel
theorem x63_residual_checked : ∀ j : Variables, scaledIntegerCheck x63_integer.scale (x63.remainder j) (integerCoeff x63_integer.residual j) = true := by decide +kernel
theorem x63_rhs_checked : ∀ i : Fin x63.support.size, scaledProductCheck x63_integer.scale (x63.multiplier i) (x63.cachedRhs literalRhs i) x63_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x63_box_checked : ∀ j : Variables, scaledProductCheck x63_integer.scale (x63.remainder j) (lower j) x63_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x63_integer.scale (x63.remainder j) (upper j) x63_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x63_bound_checked : scaledIntegerCheck x63_integer.scale x63.bound x63_integer.bound = true := by decide +kernel
theorem x63_sum_checked : x63_integer.bound ≤ (∑ i : Fin x63.support.size, x63_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x63_integer.lowerProducts[j.val]! x63_integer.upperProducts[j.val]! := by decide +kernel
theorem x63_coeff00_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff01_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff02_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff03_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff04_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff05_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff06_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff07_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff08_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff09_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff10_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff11_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff12_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff13_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff14_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff15_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff16_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff17_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff18_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff19_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff20_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff21_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff22_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff23_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff24_checked : ∀ j : Fin 16, integerCoeff x63_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coeff25_checked : ∀ j : Fin 2, integerCoeff x63_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x63_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x63_coefficients_checked : ∀ j : Variables, integerCoeff x63_expansion j = integerCoeff x63_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x63_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x63_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x63_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x63_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x63_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x63_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x63_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x63_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x63_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x63_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x63_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x63_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x63_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x63_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x63_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x63_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x63_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x63_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x63_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x63_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x63_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x63_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x63_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x63_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x63_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x63_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x63_integer_checked : x63_integer.flatCoeffCheck x63 literalRows literalTerms literalRhs (baseCount+63) x63_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x63_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x63_indices_checked, x63_sign_checked⟩, x63_objective_checked⟩, x63_rows_checked⟩, x63_coefficients_checked⟩, x63_residual_checked⟩, x63_rhs_checked⟩, x63_box_checked⟩, x63_bound_checked⟩, x63_sum_checked⟩⟩
theorem x63_checked : x63.checkCached rows cachedTerms cachedRhs (baseCount+63) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x63_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x63_checked
end OptimalG.UniversalLP.Data
