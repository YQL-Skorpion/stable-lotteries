import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x55 : DualProposal where
  support := #[(339, (-5426987378407697 / 3051757812500000))]
  objective := [(141, 1), (59, (-1253712231 / 1000000000))]
  residual := #[(-765205220355485277 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (2478548679 / 1220703125000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x55_sparseResidual : Terms := [(0, (-765205220355485277 / 610351562500000000)), (59, (2478548679 / 1220703125000000000)), (141, (-25401 / 305175781250000000000))]
def x55_integer : IntegerDualCertificate where
  scale := 6103515625000000000000000000
  objective := [(141, 6103515625000000000000000000), (59, (-7652052191162109375000000000))]
  weightedRows := #[[(59, 7652052203554852770000000000), (0, (-7652052203554852770000000000)), (141, (-6103515625000000508020000000))]]
  residual := [(0, (-7652052203554852770000000000)), (59, 12392743395000000000), (141, (-508020000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 744120418241265750, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-43486588203), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1516560114051615750, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-75151474803), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x55_expansion : IntegerTerms := [(141, 6103515625000000000000000000), (59, (-7652052191162109375000000000)), (59, 7652052203554852770000000000), (0, (-7652052203554852770000000000)), (141, (-6103515625000000508020000000))]
theorem x55_indices_checked : 0 < x55_integer.scale ∧ (baseCount+55) ≤ literalRows.size ∧ ∀ i, x55.rowIndex i < (baseCount+55) := by decide +kernel
theorem x55_sign_checked : ∀ i, x55.multiplier i ≤ 0 := by decide +kernel
theorem x55_objective_checked : scaledTermsCheck x55_integer.scale 1 x55.objective x55_integer.objective = true := by decide +kernel
theorem x55_rows_checked : ∀ i : Fin x55.support.size, scaledTermsCheck x55_integer.scale (-x55.multiplier i) literalTerms[x55.rowIndex i]! x55_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x55_expansion_checked : x55_integer.expanded x55 = x55_expansion := by decide +kernel
theorem x55_residual_checked : ∀ j : Variables, scaledIntegerCheck x55_integer.scale (x55.remainder j) (integerCoeff x55_integer.residual j) = true := by decide +kernel
theorem x55_rhs_checked : ∀ i : Fin x55.support.size, scaledProductCheck x55_integer.scale (x55.multiplier i) (x55.cachedRhs literalRhs i) x55_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x55_box_checked : ∀ j : Variables, scaledProductCheck x55_integer.scale (x55.remainder j) (lower j) x55_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x55_integer.scale (x55.remainder j) (upper j) x55_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x55_bound_checked : scaledIntegerCheck x55_integer.scale x55.bound x55_integer.bound = true := by decide +kernel
theorem x55_sum_checked : x55_integer.bound ≤ (∑ i : Fin x55.support.size, x55_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x55_integer.lowerProducts[j.val]! x55_integer.upperProducts[j.val]! := by decide +kernel
theorem x55_coeff00_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff01_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff02_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff03_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff04_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff05_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff06_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff07_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff08_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff09_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff10_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff11_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff12_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff13_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff14_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff15_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff16_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff17_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff18_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff19_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff20_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff21_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff22_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff23_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff24_checked : ∀ j : Fin 16, integerCoeff x55_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coeff25_checked : ∀ j : Fin 2, integerCoeff x55_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x55_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x55_coefficients_checked : ∀ j : Variables, integerCoeff x55_expansion j = integerCoeff x55_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x55_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x55_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x55_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x55_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x55_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x55_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x55_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x55_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x55_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x55_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x55_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x55_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x55_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x55_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x55_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x55_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x55_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x55_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x55_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x55_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x55_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x55_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x55_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x55_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x55_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x55_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x55_integer_checked : x55_integer.flatCoeffCheck x55 literalRows literalTerms literalRhs (baseCount+55) x55_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x55_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x55_indices_checked, x55_sign_checked⟩, x55_objective_checked⟩, x55_rows_checked⟩, x55_coefficients_checked⟩, x55_residual_checked⟩, x55_rhs_checked⟩, x55_box_checked⟩, x55_bound_checked⟩, x55_sum_checked⟩⟩
theorem x55_checked : x55.checkCached rows cachedTerms cachedRhs (baseCount+55) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x55_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x55_checked
end OptimalG.UniversalLP.Data
