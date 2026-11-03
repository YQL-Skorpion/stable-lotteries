import OptimalG.UniversalLPData.LiteralCache
import OptimalG.UniversalLPIntegerFlatCheck
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def x17 : DualProposal where
  support := #[(6, (-9631 / 100000000000000000000)), (56, (-32111 / 1250000000000000000)), (58, (-1199903 / 50000000000000000000)), (333, (-5426987378407611 / 3051757812500000)), (334, (-2792913 / 100000000000000000000)), (356, (-797789 / 25000000000000000000))]
  objective := [(137, 1), (63, (-2436291853 / 2000000000))]
  residual := #[(-2436291857094588724497 / 2000000000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (90997 / 10000000000000000000000), (639779485359 / 312500000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (84537 / 50000000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (4810637 / 305175781250000000000), (-157053876729 / 10000000000000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-29105736087 / 2500000000000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (128444029 / 25000000000000000000), (-128444029 / 25000000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-29 / 25000000000000000000), (-119990271 / 25000000000000000000), (1199903 / 250000000000000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x17_sparseResidual : Terms := [(0, (-2436291857094588724497 / 2000000000000000000000)), (62, (90997 / 10000000000000000000000)), (63, (639779485359 / 312500000000000000000)), (79, (84537 / 50000000000000000000)), (137, (4810637 / 305175781250000000000)), (138, (-157053876729 / 10000000000000000000000000)), (161, (-29105736087 / 2500000000000000000000000)), (240, (128444029 / 25000000000000000000)), (241, (-128444029 / 25000000000000000000)), (279, (-29 / 25000000000000000000)), (280, (-119990271 / 25000000000000000000)), (281, (1199903 / 250000000000000000))]
def x17_integer : IntegerDualCertificate where
  scale := 37500000000000000000000000000000000
  objective := [(137, 37500000000000000000000000000000000), (63, (-45680472243750000000000000000000000))]
  weightedRows := #[[(63, 722325000000000000000), (62, (-722325000000000000000))], [(280, (-192666000000000000000000)), (279, 192666000000000000000000), (79, 963330000000000000000)], [(281, 179985450000000000000000), (280, (-179985450000000000000000)), (79, (-899927250000000000000))], [(63, 45680472320522815918080000000000000), (0, (-45680472320522815918080000000000000)), (137, (-37499999999999408868925440000000000))], [(62, 722666238750000000000), (0, (-722666238750000000000)), (138, (-588952037733750000000))], [(280, 192666043500000000000000), (279, (-192666043500000000000000)), (241, (-192666043500000000000000)), (240, 192666043500000000000000), (161, (-436586041305000000000))]]
  residual := [(0, (-45680472320523538584318750000000000)), (62, 341238750000000000), (63, 76773538243080000000000000), (79, 63402750000000000000), (137, 591131074560000000000), (138, (-588952037733750000000)), (161, (-436586041305000000000)), (240, 192666043500000000000000), (241, (-192666043500000000000000)), (279, (-43500000000000000)), (280, (-179985406500000000000000)), (281, 179985450000000000000000)]
  rhsProducts := #[(-902292273750000000), (-406998897250000000), (-372712369981250000), 0, 0, 0]
  lowerProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21819590524125000, 5004978279696837666000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5184940579087500000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52169415845234688000, (-51608512476921724875), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-28960127365790760750), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 197430602334259020727, (-225584899298665833227), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-534771143211227), (-2285880589544095570173), 2359847970041422968900, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  upperProducts := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43089001811625000, 9790272918388014066000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9136833986587500000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89014615722559488000, (-88317892988866362375), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-56172535320331410750), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1821751197405918187500, (-1909949866827100000000), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1430223297750000), (-6046991892881243062500), 6177052647880000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  bound := 0
def x17_expansion : IntegerTerms := [(137, 37500000000000000000000000000000000), (63, (-45680472243750000000000000000000000)), (63, 722325000000000000000), (62, (-722325000000000000000)), (280, (-192666000000000000000000)), (279, 192666000000000000000000), (79, 963330000000000000000), (281, 179985450000000000000000), (280, (-179985450000000000000000)), (79, (-899927250000000000000)), (63, 45680472320522815918080000000000000), (0, (-45680472320522815918080000000000000)), (137, (-37499999999999408868925440000000000)), (62, 722666238750000000000), (0, (-722666238750000000000)), (138, (-588952037733750000000)), (280, 192666043500000000000000), (279, (-192666043500000000000000)), (241, (-192666043500000000000000)), (240, 192666043500000000000000), (161, (-436586041305000000000))]
theorem x17_indices_checked : 0 < x17_integer.scale ∧ (baseCount+17) ≤ literalRows.size ∧ ∀ i, x17.rowIndex i < (baseCount+17) := by decide +kernel
theorem x17_sign_checked : ∀ i, x17.multiplier i ≤ 0 := by decide +kernel
theorem x17_objective_checked : scaledTermsCheck x17_integer.scale 1 x17.objective x17_integer.objective = true := by decide +kernel
theorem x17_rows_checked : ∀ i : Fin x17.support.size, scaledTermsCheck x17_integer.scale (-x17.multiplier i) literalTerms[x17.rowIndex i]! x17_integer.weightedRows[i.val]! = true := by decide +kernel
theorem x17_expansion_checked : x17_integer.expanded x17 = x17_expansion := by decide +kernel
theorem x17_residual_checked : ∀ j : Variables, scaledIntegerCheck x17_integer.scale (x17.remainder j) (integerCoeff x17_integer.residual j) = true := by decide +kernel
theorem x17_rhs_checked : ∀ i : Fin x17.support.size, scaledProductCheck x17_integer.scale (x17.multiplier i) (x17.cachedRhs literalRhs i) x17_integer.rhsProducts[i.val]! = true := by decide +kernel
theorem x17_box_checked : ∀ j : Variables, scaledProductCheck x17_integer.scale (x17.remainder j) (lower j) x17_integer.lowerProducts[j.val]! = true ∧ scaledProductCheck x17_integer.scale (x17.remainder j) (upper j) x17_integer.upperProducts[j.val]! = true := by decide +kernel
theorem x17_bound_checked : scaledIntegerCheck x17_integer.scale x17.bound x17_integer.bound = true := by decide +kernel
theorem x17_sum_checked : x17_integer.bound ≤ (∑ i : Fin x17.support.size, x17_integer.rhsProducts[i.val]!) + ∑ j : Variables, min x17_integer.lowerProducts[j.val]! x17_integer.upperProducts[j.val]! := by decide +kernel
theorem x17_coeff00_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨0+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff01_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨16+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff02_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨32+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff03_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨48+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff04_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨64+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff05_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨80+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff06_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨96+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff07_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨112+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff08_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨128+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff09_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨144+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff10_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨160+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff11_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨176+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff12_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨192+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff13_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨208+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff14_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨224+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff15_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨240+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff16_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨256+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff17_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨272+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff18_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨288+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff19_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨304+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff20_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨320+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff21_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨336+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff22_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨352+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff23_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨368+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff24_checked : ∀ j : Fin 16, integerCoeff x17_expansion (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨384+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coeff25_checked : ∀ j : Fin 2, integerCoeff x17_expansion (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) = integerCoeff x17_integer.residual (⟨400+j.val, by have := j.isLt; omega⟩ : Variables) := by decide +kernel
theorem x17_coefficients_checked : ∀ j : Variables, integerCoeff x17_expansion j = integerCoeff x17_integer.residual j := by
  intro j
  have hj := j.isLt
  have hk : j.val / 16 ≤ 25 := by omega
  interval_cases h : j.val / 16
  · have hi : 0+j.val%16=j.val := by omega
    have hc := x17_coeff00_checked ⟨j.val%16,by omega⟩
    have heq : (⟨0+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 16+j.val%16=j.val := by omega
    have hc := x17_coeff01_checked ⟨j.val%16,by omega⟩
    have heq : (⟨16+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 32+j.val%16=j.val := by omega
    have hc := x17_coeff02_checked ⟨j.val%16,by omega⟩
    have heq : (⟨32+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 48+j.val%16=j.val := by omega
    have hc := x17_coeff03_checked ⟨j.val%16,by omega⟩
    have heq : (⟨48+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 64+j.val%16=j.val := by omega
    have hc := x17_coeff04_checked ⟨j.val%16,by omega⟩
    have heq : (⟨64+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 80+j.val%16=j.val := by omega
    have hc := x17_coeff05_checked ⟨j.val%16,by omega⟩
    have heq : (⟨80+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 96+j.val%16=j.val := by omega
    have hc := x17_coeff06_checked ⟨j.val%16,by omega⟩
    have heq : (⟨96+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 112+j.val%16=j.val := by omega
    have hc := x17_coeff07_checked ⟨j.val%16,by omega⟩
    have heq : (⟨112+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 128+j.val%16=j.val := by omega
    have hc := x17_coeff08_checked ⟨j.val%16,by omega⟩
    have heq : (⟨128+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 144+j.val%16=j.val := by omega
    have hc := x17_coeff09_checked ⟨j.val%16,by omega⟩
    have heq : (⟨144+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 160+j.val%16=j.val := by omega
    have hc := x17_coeff10_checked ⟨j.val%16,by omega⟩
    have heq : (⟨160+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 176+j.val%16=j.val := by omega
    have hc := x17_coeff11_checked ⟨j.val%16,by omega⟩
    have heq : (⟨176+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 192+j.val%16=j.val := by omega
    have hc := x17_coeff12_checked ⟨j.val%16,by omega⟩
    have heq : (⟨192+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 208+j.val%16=j.val := by omega
    have hc := x17_coeff13_checked ⟨j.val%16,by omega⟩
    have heq : (⟨208+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 224+j.val%16=j.val := by omega
    have hc := x17_coeff14_checked ⟨j.val%16,by omega⟩
    have heq : (⟨224+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 240+j.val%16=j.val := by omega
    have hc := x17_coeff15_checked ⟨j.val%16,by omega⟩
    have heq : (⟨240+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 256+j.val%16=j.val := by omega
    have hc := x17_coeff16_checked ⟨j.val%16,by omega⟩
    have heq : (⟨256+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 272+j.val%16=j.val := by omega
    have hc := x17_coeff17_checked ⟨j.val%16,by omega⟩
    have heq : (⟨272+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 288+j.val%16=j.val := by omega
    have hc := x17_coeff18_checked ⟨j.val%16,by omega⟩
    have heq : (⟨288+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 304+j.val%16=j.val := by omega
    have hc := x17_coeff19_checked ⟨j.val%16,by omega⟩
    have heq : (⟨304+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 320+j.val%16=j.val := by omega
    have hc := x17_coeff20_checked ⟨j.val%16,by omega⟩
    have heq : (⟨320+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 336+j.val%16=j.val := by omega
    have hc := x17_coeff21_checked ⟨j.val%16,by omega⟩
    have heq : (⟨336+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 352+j.val%16=j.val := by omega
    have hc := x17_coeff22_checked ⟨j.val%16,by omega⟩
    have heq : (⟨352+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 368+j.val%16=j.val := by omega
    have hc := x17_coeff23_checked ⟨j.val%16,by omega⟩
    have heq : (⟨368+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 384+j.val%16=j.val := by omega
    have hc := x17_coeff24_checked ⟨j.val%16,by omega⟩
    have heq : (⟨384+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
  · have hi : 400+j.val%16=j.val := by omega
    have hc := x17_coeff25_checked ⟨j.val%16,by omega⟩
    have heq : (⟨400+j.val%16, by omega⟩ : Variables) = j := Fin.ext hi
    simpa only [heq] using hc
theorem x17_integer_checked : x17_integer.flatCoeffCheck x17 literalRows literalTerms literalRhs (baseCount+17) x17_expansion = true := by
  simp only [IntegerDualCertificate.flatCoeffCheck,IntegerDualCertificate.checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq]
  exact ⟨x17_expansion_checked, ⟨⟨⟨⟨⟨⟨⟨⟨⟨x17_indices_checked, x17_sign_checked⟩, x17_objective_checked⟩, x17_rows_checked⟩, x17_coefficients_checked⟩, x17_residual_checked⟩, x17_rhs_checked⟩, x17_box_checked⟩, x17_bound_checked⟩, x17_sum_checked⟩⟩
theorem x17_checked : x17.checkCached rows cachedTerms cachedRhs (baseCount+17) = true := by
  have hc := IntegerDualCertificate.checkCached_of_flatCoeffCheck x17_integer_checked
  simpa only [literalRows_eq,literalTerms_eq,literalRhs_eq] using hc
#print axioms x17_checked
end OptimalG.UniversalLP.Data
