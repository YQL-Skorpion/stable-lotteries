import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x32 : DualProposal where
  support := #[(347, (-5426987378407697 / 3051757812500000))]
  objective := [(146, 1), (54, (-3245425279 / 2500000000))]
  residual := #[(-396170078623761881 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1241664387 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x32_sparseResidual : Terms := [(0, (-396170078623761881 / 305175781250000000)), (54, (1241664387 / 610351562500000000)), (146, (-25401 / 305175781250000000000))]
def x32_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000))]
  weightedRows := #[[(54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]]
  residual := [(0, (-3961700786237618810000000000)), (54, 6208321935000000000), (146, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 329345891162008500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-20757925809), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 716310597370558500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-36590369109), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x32_expansion : IntegerTerms := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000)), (54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]
theorem x32_indices_checked : 0 < x32_integer.scale ∧ (baseCount+32) ≤ literalRows.size ∧ ∀ i, x32.rowIndex i < (baseCount+32) := by decide +kernel
theorem x32_sign_checked : ∀ i, x32.multiplier i ≤ 0 := by decide +kernel
theorem x32_objective_checked : scaledTermsCheck x32_integer.scale 1 x32.objective x32_integer.objective = true := by decide +kernel
theorem x32_rows_checked : ∀ i : Fin x32.support.size, scaledTermsCheck x32_integer.scale (-x32.multiplier i) literalTerms[x32.rowIndex i]! x32_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x32_expansion_checked : x32_integer.expanded x32 = x32_expansion := by decide +kernel
theorem x32_residual_checked : ∀ j : Variables, scaledIntegerCheck x32_integer.scale (x32.remainder j) (integerCoeff x32_integer.residual j) = true := by decide +kernel
theorem x32_rhs_checked : ∀ i : Fin x32.support.size, scaledProductCheck x32_integer.scale (x32.multiplier i) (x32.cachedRhs literalRhs i) x32_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x32_box_checked : ∀ j : Variables, scaledProductCheck x32_integer.scale (x32.remainder j) (lower j) x32_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x32_integer.scale (x32.remainder j) (upper j) x32_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x32_bound_checked : scaledIntegerCheck x32_integer.scale x32.bound x32_integer.bound = true := by decide +kernel
theorem x32_sum_checked : x32_integer.bound ≤ (∑ i : Fin x32.support.size, x32_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x32_integer.lowerProducts[j.val]! x32_integer.upperProducts[j.val]! := by decide +kernel
theorem x32_coeff00_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff01_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff02_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff03_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff04_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff05_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff06_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff07_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff08_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff09_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff10_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff11_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff12_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff13_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff14_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff15_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff16_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff17_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff18_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff19_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff20_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff21_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff22_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff23_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff24_checked : ∀ j : Fin 16, integerCoeff x32_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coeff25_checked : ∀ j : Fin 2, integerCoeff x32_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x32_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x32_coefficients_checked : ∀ j : Variables, integerCoeff x32_expansion j = integerCoeff x32_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x32_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x32_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x32_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x32_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x32_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x32_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x32_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x32_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x32_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x32_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x32_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x32_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x32_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x32_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x32_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x32_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x32_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x32_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x32_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x32_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x32_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x32_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x32_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x32_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x32_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x32_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x32_integer_checked : x32_integer.flatCoeffCheck x32 literalRows literalTerms literalRhs (baseCount+32) x32_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x32_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x32_indices_checked, x32_sign_checked⟩, x32_objective_checked⟩, x32_rows_checked⟩, x32_coefficients_checked⟩, x32_residual_checked⟩, x32_rhs_checked⟩, x32_box_checked⟩, x32_bound_checked⟩, x32_sum_checked⟩⟩
theorem x32_checked : x32.checkCached rows cachedTerms cachedRhs (baseCount+32) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x32_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x32_checked
end OptimalG.UniversalLP.Data
