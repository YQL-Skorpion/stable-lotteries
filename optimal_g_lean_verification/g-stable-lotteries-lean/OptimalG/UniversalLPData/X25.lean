import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x25 : DualProposal where
  support := #[(342, (-5426987378407697 / 3051757812500000))]
  objective := [(143, 1), (57, (-1589369229 / 1250000000))]
  residual := #[(-776059195112300671 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1264644421 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x25_sparseResidual : Terms := [(0, (-776059195112300671 / 610351562500000000)), (57, (1264644421 / 610351562500000000)), (143, (-25401 / 305175781250000000000))]
def x25_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(143, 6103515625000000000000000000), (57, (-7760591938476562500000000000))]
  weightedRows := #[[(57, 7760591951123006710000000000), (0, (-7760591951123006710000000000)), (143, (-6103515625000000508020000000))]]
  residual := [(0, (-7760591951123006710000000000)), (57, 12646444210000000000), (143, (-508020000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 724913784105725500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-42736395069), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1513166651715025500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-74401281669), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x25_expansion : IntegerTerms := [(143, 6103515625000000000000000000), (57, (-7760591938476562500000000000)), (57, 7760591951123006710000000000), (0, (-7760591951123006710000000000)), (143, (-6103515625000000508020000000))]
theorem x25_indices_checked : 0 < x25_integer.scale ∧ (baseCount+25) ≤ literalRows.size ∧ ∀ i, x25.rowIndex i < (baseCount+25) := by decide +kernel
theorem x25_sign_checked : ∀ i, x25.multiplier i ≤ 0 := by decide +kernel
theorem x25_objective_checked : scaledTermsCheck x25_integer.scale 1 x25.objective x25_integer.objective = true := by decide +kernel
theorem x25_rows_checked : ∀ i : Fin x25.support.size, scaledTermsCheck x25_integer.scale (-x25.multiplier i) literalTerms[x25.rowIndex i]! x25_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x25_expansion_checked : x25_integer.expanded x25 = x25_expansion := by decide +kernel
theorem x25_residual_checked : ∀ j : Variables, scaledIntegerCheck x25_integer.scale (x25.remainder j) (integerCoeff x25_integer.residual j) = true := by decide +kernel
theorem x25_rhs_checked : ∀ i : Fin x25.support.size, scaledProductCheck x25_integer.scale (x25.multiplier i) (x25.cachedRhs literalRhs i) x25_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x25_box_checked : ∀ j : Variables, scaledProductCheck x25_integer.scale (x25.remainder j) (lower j) x25_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x25_integer.scale (x25.remainder j) (upper j) x25_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x25_bound_checked : scaledIntegerCheck x25_integer.scale x25.bound x25_integer.bound = true := by decide +kernel
theorem x25_sum_checked : x25_integer.bound ≤ (∑ i : Fin x25.support.size, x25_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x25_integer.lowerProducts[j.val]! x25_integer.upperProducts[j.val]! := by decide +kernel
theorem x25_coeff00_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff01_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff02_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff03_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff04_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff05_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff06_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff07_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff08_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff09_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff10_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff11_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff12_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff13_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff14_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff15_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff16_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff17_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff18_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff19_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff20_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff21_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff22_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff23_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff24_checked : ∀ j : Fin 16, integerCoeff x25_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coeff25_checked : ∀ j : Fin 2, integerCoeff x25_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x25_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x25_coefficients_checked : ∀ j : Variables, integerCoeff x25_expansion j = integerCoeff x25_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x25_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x25_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x25_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x25_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x25_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x25_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x25_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x25_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x25_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x25_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x25_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x25_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x25_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x25_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x25_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x25_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x25_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x25_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x25_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x25_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x25_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x25_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x25_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x25_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x25_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x25_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x25_integer_checked : x25_integer.flatCoeffCheck x25 literalRows literalTerms literalRhs (baseCount+25) x25_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x25_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x25_indices_checked, x25_sign_checked⟩, x25_objective_checked⟩, x25_rows_checked⟩, x25_coefficients_checked⟩, x25_residual_checked⟩, x25_rhs_checked⟩, x25_box_checked⟩, x25_bound_checked⟩, x25_sum_checked⟩⟩
theorem x25_checked : x25.checkCached rows cachedTerms cachedRhs (baseCount+25) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x25_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x25_checked
end OptimalG.UniversalLP.Data
