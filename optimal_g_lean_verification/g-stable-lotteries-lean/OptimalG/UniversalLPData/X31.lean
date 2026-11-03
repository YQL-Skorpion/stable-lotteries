import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x31 : DualProposal where
  support := #[(347, (-5426987378407697 / 3051757812500000))]
  objective := [(146, 1), (54, (-3245425279 / 2500000000))]
  residual := #[(-396170078623761881 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1241664387 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x31_sparseResidual : Terms := [(0, (-396170078623761881 / 305175781250000000)), (54, (1241664387 / 610351562500000000)), (146, (-25401 / 305175781250000000000))]
def x31_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000))]
  weightedRows := #[[(54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]]
  residual := [(0, (-3961700786237618810000000000)), (54, 6208321935000000000), (146, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 329345891162008500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-20757925809), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 716310597370558500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-36590369109), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x31_expansion : IntegerTerms := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000)), (54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]
theorem x31_indices_checked : 0 < x31_integer.scale ∧ (baseCount+31) ≤ literalRows.size ∧ ∀ i, x31.rowIndex i < (baseCount+31) := by decide +kernel
theorem x31_sign_checked : ∀ i, x31.multiplier i ≤ 0 := by decide +kernel
theorem x31_objective_checked : scaledTermsCheck x31_integer.scale 1 x31.objective x31_integer.objective = true := by decide +kernel
theorem x31_rows_checked : ∀ i : Fin x31.support.size, scaledTermsCheck x31_integer.scale (-x31.multiplier i) literalTerms[x31.rowIndex i]! x31_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x31_expansion_checked : x31_integer.expanded x31 = x31_expansion := by decide +kernel
theorem x31_residual_checked : ∀ j : Variables, scaledIntegerCheck x31_integer.scale (x31.remainder j) (integerCoeff x31_integer.residual j) = true := by decide +kernel
theorem x31_rhs_checked : ∀ i : Fin x31.support.size, scaledProductCheck x31_integer.scale (x31.multiplier i) (x31.cachedRhs literalRhs i) x31_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x31_box_checked : ∀ j : Variables, scaledProductCheck x31_integer.scale (x31.remainder j) (lower j) x31_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x31_integer.scale (x31.remainder j) (upper j) x31_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x31_bound_checked : scaledIntegerCheck x31_integer.scale x31.bound x31_integer.bound = true := by decide +kernel
theorem x31_sum_checked : x31_integer.bound ≤ (∑ i : Fin x31.support.size, x31_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x31_integer.lowerProducts[j.val]! x31_integer.upperProducts[j.val]! := by decide +kernel
theorem x31_coeff00_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff01_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff02_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff03_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff04_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff05_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff06_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff07_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff08_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff09_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff10_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff11_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff12_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff13_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff14_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff15_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff16_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff17_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff18_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff19_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff20_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff21_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff22_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff23_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff24_checked : ∀ j : Fin 16, integerCoeff x31_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coeff25_checked : ∀ j : Fin 2, integerCoeff x31_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x31_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x31_coefficients_checked : ∀ j : Variables, integerCoeff x31_expansion j = integerCoeff x31_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x31_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x31_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x31_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x31_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x31_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x31_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x31_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x31_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x31_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x31_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x31_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x31_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x31_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x31_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x31_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x31_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x31_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x31_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x31_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x31_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x31_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x31_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x31_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x31_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x31_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x31_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x31_integer_checked : x31_integer.flatCoeffCheck x31 literalRows literalTerms literalRhs (baseCount+31) x31_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x31_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x31_indices_checked, x31_sign_checked⟩, x31_objective_checked⟩, x31_rows_checked⟩, x31_coefficients_checked⟩, x31_residual_checked⟩, x31_rhs_checked⟩, x31_box_checked⟩, x31_bound_checked⟩, x31_sum_checked⟩⟩
theorem x31_checked : x31.checkCached rows cachedTerms cachedRhs (baseCount+31) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x31_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x31_checked
end OptimalG.UniversalLP.Data
