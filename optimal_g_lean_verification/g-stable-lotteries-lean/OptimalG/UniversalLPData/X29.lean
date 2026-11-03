import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x29 : DualProposal where
  support := #[(345, (-5426987378407697 / 3051757812500000))]
  objective := [(145, 1), (55, (-2578557071 / 2000000000))]
  residual := #[(-157382633973823213 / 122070312500000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (983183477 / 488281250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-25401 / 305175781250000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x29_sparseResidual : Terms := [(0, (-157382633973823213 / 122070312500000000)), (55, (983183477 / 488281250000000000)), (145, (-25401 / 305175781250000000000))]
def x29_integer : IntegerDualCertificate where
  scale := 1220703125000000000000000000
  objective := [(145, 1220703125000000000000000000), (55, (-1573826337280273437500000000))]
  weightedRows := #[[(55, 1573826339738232130000000000), (0, (-1573826339738232130000000000)), (145, (-1220703125000000101604000000))]]
  residual := [(0, (-1573826339738232130000000000)), (55, 2457958692500000000), (145, (-101604000000))]
  rhsProducts := #[0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133954447313538125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-8387079987), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 287159012617063125, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-14720057307), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x29_expansion : IntegerTerms := [(145, 1220703125000000000000000000), (55, (-1573826337280273437500000000)), (55, 1573826339738232130000000000), (0, (-1573826339738232130000000000)), (145, (-1220703125000000101604000000))]
theorem x29_indices_checked : 0 < x29_integer.scale ∧ (baseCount+29) ≤ literalRows.size ∧ ∀ i, x29.rowIndex i < (baseCount+29) := by decide +kernel
theorem x29_sign_checked : ∀ i, x29.multiplier i ≤ 0 := by decide +kernel
theorem x29_objective_checked : scaledTermsCheck x29_integer.scale 1 x29.objective x29_integer.objective = true := by decide +kernel
theorem x29_rows_checked : ∀ i : Fin x29.support.size, scaledTermsCheck x29_integer.scale (-x29.multiplier i) literalTerms[x29.rowIndex i]! x29_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x29_expansion_checked : x29_integer.expanded x29 = x29_expansion := by decide +kernel
theorem x29_residual_checked : ∀ j : Variables, scaledIntegerCheck x29_integer.scale (x29.remainder j) (integerCoeff x29_integer.residual j) = true := by decide +kernel
theorem x29_rhs_checked : ∀ i : Fin x29.support.size, scaledProductCheck x29_integer.scale (x29.multiplier i) (x29.cachedRhs literalRhs i) x29_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x29_box_checked : ∀ j : Variables, scaledProductCheck x29_integer.scale (x29.remainder j) (lower j) x29_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x29_integer.scale (x29.remainder j) (upper j) x29_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x29_bound_checked : scaledIntegerCheck x29_integer.scale x29.bound x29_integer.bound = true := by decide +kernel
theorem x29_sum_checked : x29_integer.bound ≤ (∑ i : Fin x29.support.size, x29_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x29_integer.lowerProducts[j.val]! x29_integer.upperProducts[j.val]! := by decide +kernel
theorem x29_coeff00_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff01_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff02_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff03_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff04_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff05_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff06_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff07_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff08_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff09_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff10_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff11_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff12_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff13_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff14_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff15_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff16_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff17_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff18_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff19_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff20_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff21_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff22_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff23_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff24_checked : ∀ j : Fin 16, integerCoeff x29_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coeff25_checked : ∀ j : Fin 2, integerCoeff x29_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x29_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x29_coefficients_checked : ∀ j : Variables, integerCoeff x29_expansion j = integerCoeff x29_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x29_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x29_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x29_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x29_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x29_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x29_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x29_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x29_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x29_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x29_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x29_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x29_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x29_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x29_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x29_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x29_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x29_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x29_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x29_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x29_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x29_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x29_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x29_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x29_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x29_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x29_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x29_integer_checked : x29_integer.flatCoeffCheck x29 literalRows literalTerms literalRhs (baseCount+29) x29_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x29_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x29_indices_checked, x29_sign_checked⟩, x29_objective_checked⟩, x29_rows_checked⟩, x29_coefficients_checked⟩, x29_residual_checked⟩, x29_rhs_checked⟩, x29_box_checked⟩, x29_bound_checked⟩, x29_sum_checked⟩⟩
theorem x29_checked : x29.checkCached rows cachedTerms cachedRhs (baseCount+29) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x29_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x29_checked
end OptimalG.UniversalLP.Data
