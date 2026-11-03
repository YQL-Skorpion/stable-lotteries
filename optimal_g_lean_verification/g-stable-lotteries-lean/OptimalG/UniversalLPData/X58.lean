import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x58 : DualProposal where
  support := #[(342, (-5426987378407697 / 3051757812500000))]
  objective := [(143, 1), (57, (-1589369229 / 1250000000))]
  residual := #[(-776059195112300671 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1264644421 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x58_sparseResidual : Terms := [(0, (-776059195112300671 / 610351562500000000)), (57, (1264644421 / 610351562500000000)), (143, (-25401 / 305175781250000000000))]
def x58_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(143, 6103515625000000000000000000), (57, (-7760591938476562500000000000))]
  weightedRows := #[[(57, 7760591951123006710000000000), (0, (-7760591951123006710000000000)), (143, (-6103515625000000508020000000))]]
  residual := [(0, (-7760591951123006710000000000)), (57, 12646444210000000000), (143, (-508020000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 724913784105725500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-42736395069), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1513166651715025500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-74401281669), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x58_expansion : IntegerTerms := [(143, 6103515625000000000000000000), (57, (-7760591938476562500000000000)), (57, 7760591951123006710000000000), (0, (-7760591951123006710000000000)), (143, (-6103515625000000508020000000))]
theorem x58_indices_checked : 0 < x58_integer.scale ∧ (baseCount+58) ≤ literalRows.size ∧ ∀ i, x58.rowIndex i < (baseCount+58) := by decide +kernel
theorem x58_sign_checked : ∀ i, x58.multiplier i ≤ 0 := by decide +kernel
theorem x58_objective_checked : scaledTermsCheck x58_integer.scale 1 x58.objective x58_integer.objective = true := by decide +kernel
theorem x58_rows_checked : ∀ i : Fin x58.support.size, scaledTermsCheck x58_integer.scale (-x58.multiplier i) literalTerms[x58.rowIndex i]! x58_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x58_expansion_checked : x58_integer.expanded x58 = x58_expansion := by decide +kernel
theorem x58_residual_checked : ∀ j : Variables, scaledIntegerCheck x58_integer.scale (x58.remainder j) (integerCoeff x58_integer.residual j) = true := by decide +kernel
theorem x58_rhs_checked : ∀ i : Fin x58.support.size, scaledProductCheck x58_integer.scale (x58.multiplier i) (x58.cachedRhs literalRhs i) x58_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x58_box_checked : ∀ j : Variables, scaledProductCheck x58_integer.scale (x58.remainder j) (lower j) x58_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x58_integer.scale (x58.remainder j) (upper j) x58_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x58_bound_checked : scaledIntegerCheck x58_integer.scale x58.bound x58_integer.bound = true := by decide +kernel
theorem x58_sum_checked : x58_integer.bound ≤ (∑ i : Fin x58.support.size, x58_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x58_integer.lowerProducts[j.val]! x58_integer.upperProducts[j.val]! := by decide +kernel
theorem x58_coeff00_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff01_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff02_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff03_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff04_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff05_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff06_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff07_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff08_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff09_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff10_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff11_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff12_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff13_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff14_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff15_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff16_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff17_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff18_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff19_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff20_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff21_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff22_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff23_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff24_checked : ∀ j : Fin 16, integerCoeff x58_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coeff25_checked : ∀ j : Fin 2, integerCoeff x58_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x58_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x58_coefficients_checked : ∀ j : Variables, integerCoeff x58_expansion j = integerCoeff x58_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x58_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x58_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x58_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x58_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x58_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x58_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x58_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x58_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x58_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x58_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x58_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x58_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x58_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x58_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x58_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x58_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x58_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x58_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x58_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x58_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x58_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x58_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x58_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x58_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x58_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x58_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x58_integer_checked : x58_integer.flatCoeffCheck x58 literalRows literalTerms literalRhs (baseCount+58) x58_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x58_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x58_indices_checked, x58_sign_checked⟩, x58_objective_checked⟩, x58_rows_checked⟩, x58_coefficients_checked⟩, x58_residual_checked⟩, x58_rhs_checked⟩, x58_box_checked⟩, x58_bound_checked⟩, x58_sum_checked⟩⟩
theorem x58_checked : x58.checkCached rows cachedTerms cachedRhs (baseCount+58) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x58_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x58_checked
end OptimalG.UniversalLP.Data
