import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x64 : DualProposal where
  support := #[(347, (-5426987378407697 / 3051757812500000))]
  objective := [(146, 1), (54, (-3245425279 / 2500000000))]
  residual := #[(-396170078623761881 / 305175781250000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1241664387 / 610351562500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x64_sparseResidual : Terms := [(0, (-396170078623761881 / 305175781250000000)), (54, (1241664387 / 610351562500000000)), (146, (-25401 / 305175781250000000000))]
def x64_integer : IntegerDualCertificate where
  scale := 3051757812500000000000000000
  objective := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000))]
  weightedRows := #[[(54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]]
  residual := [(0, (-3961700786237618810000000000)), (54, 6208321935000000000), (146, (-254010000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 329345891162008500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-20757925809), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 716310597370558500, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-36590369109), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x64_expansion : IntegerTerms := [(146, 3051757812500000000000000000), (54, (-3961700780029296875000000000)), (54, 3961700786237618810000000000), (0, (-3961700786237618810000000000)), (146, (-3051757812500000254010000000))]
theorem x64_indices_checked : 0 < x64_integer.scale ∧ (baseCount+64) ≤ literalRows.size ∧ ∀ i, x64.rowIndex i < (baseCount+64) := by decide +kernel
theorem x64_sign_checked : ∀ i, x64.multiplier i ≤ 0 := by decide +kernel
theorem x64_objective_checked : scaledTermsCheck x64_integer.scale 1 x64.objective x64_integer.objective = true := by decide +kernel
theorem x64_rows_checked : ∀ i : Fin x64.support.size, scaledTermsCheck x64_integer.scale (-x64.multiplier i) literalTerms[x64.rowIndex i]! x64_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x64_expansion_checked : x64_integer.expanded x64 = x64_expansion := by decide +kernel
theorem x64_residual_checked : ∀ j : Variables, scaledIntegerCheck x64_integer.scale (x64.remainder j) (integerCoeff x64_integer.residual j) = true := by decide +kernel
theorem x64_rhs_checked : ∀ i : Fin x64.support.size, scaledProductCheck x64_integer.scale (x64.multiplier i) (x64.cachedRhs literalRhs i) x64_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x64_box_checked : ∀ j : Variables, scaledProductCheck x64_integer.scale (x64.remainder j) (lower j) x64_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x64_integer.scale (x64.remainder j) (upper j) x64_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x64_bound_checked : scaledIntegerCheck x64_integer.scale x64.bound x64_integer.bound = true := by decide +kernel
theorem x64_sum_checked : x64_integer.bound ≤ (∑ i : Fin x64.support.size, x64_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x64_integer.lowerProducts[j.val]! x64_integer.upperProducts[j.val]! := by decide +kernel
theorem x64_coeff00_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff01_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff02_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff03_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff04_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff05_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff06_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff07_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff08_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff09_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff10_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff11_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff12_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff13_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff14_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff15_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff16_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff17_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff18_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff19_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff20_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff21_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff22_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff23_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff24_checked : ∀ j : Fin 16, integerCoeff x64_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coeff25_checked : ∀ j : Fin 2, integerCoeff x64_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x64_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x64_coefficients_checked : ∀ j : Variables, integerCoeff x64_expansion j = integerCoeff x64_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x64_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x64_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x64_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x64_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x64_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x64_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x64_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x64_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x64_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x64_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x64_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x64_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x64_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x64_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x64_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x64_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x64_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x64_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x64_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x64_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x64_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x64_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x64_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x64_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x64_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x64_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x64_integer_checked : x64_integer.flatCoeffCheck x64 literalRows literalTerms literalRhs (baseCount+64) x64_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x64_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x64_indices_checked, x64_sign_checked⟩, x64_objective_checked⟩, x64_rows_checked⟩, x64_coefficients_checked⟩, x64_residual_checked⟩, x64_rhs_checked⟩, x64_box_checked⟩, x64_bound_checked⟩, x64_sum_checked⟩⟩
theorem x64_checked : x64.checkCached rows cachedTerms cachedRhs (baseCount+64) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x64_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x64_checked
end OptimalG.UniversalLP.Data
