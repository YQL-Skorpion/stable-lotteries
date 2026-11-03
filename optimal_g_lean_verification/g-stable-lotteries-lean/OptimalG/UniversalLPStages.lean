import OptimalG.UniversalIntegralRows
import OptimalG.UniversalLPCheck

/-! Semantic stage checks for the sequential universal LP certificate. -/
namespace OptimalG.UniversalLP
open Set

/-- Every non-moving row has a finite, decidable domain check. -/
def BaseRowValid : RowTag → Prop
  | .slope j => j < 200
  | .momentUp j => j < 200
  | .momentLow j => j < 200
  | .binary i j => 0 < i ∧ i < 200 ∧ j ≤ i ∧ node j ≤ L
  | .binaryIntegral i j => 0 < i ∧ i < 200 ∧ j + 1 ≤ i ∧ node (j + 1) ≤ L
  | .moving .. => False

instance (tag : RowTag) : Decidable (BaseRowValid tag) := by
  cases tag <;> unfold BaseRowValid <;> infer_instance

theorem BaseRowValid.sound {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass (L : ℝ) phi)
    {tag : RowTag} (hv : BaseRowValid tag) : RowHolds tag (gridValues phi) := by
  cases tag with
  | slope j => exact slope_row h hv
  | momentUp j => exact moment_up_row h hv
  | momentLow j => exact moment_low_row h hv
  | binary i j => exact binary_row h hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  | binaryIntegral i j => exact binary_integral_row h hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  | moving pi i j k l z0 z1 x y => exact False.elim hv

structure MovingStage where
  pi : ℕ
  i : ℕ
  j : ℕ
  k : ℕ
  l : ℕ
  z0 : ℕ
  z1 : ℕ
  x : ℚ
  y : ℚ
  xDual : DualProposal
  yDual : DualProposal
  deriving Inhabited

namespace MovingStage

def tag (s : MovingStage) : RowTag := .moving s.pi s.i s.j s.k s.l s.z0 s.z1 s.x s.y

def xObjective (s : MovingStage) : Terms := [(s.pi, 1), (200 - s.pi, -s.x)]
def yObjective (s : MovingStage) : Terms :=
  [(201 + s.z1, -200), (201 + s.z0, 200),
   (201 + (s.z1 - (200 - s.pi)), 200), (201 + (s.z0 - (200 - s.pi)), -200),
   (200 - s.pi, -s.y)]

/-- The high-bin unit width is part of the check: the y dual uses factor 200,
so this identity is essential when identifying its objective with average K. -/
def Valid (s : MovingStage) : Prop :=
  0 < s.pi ∧ s.pi < 200 ∧ s.i < s.j ∧ s.k < s.l ∧ s.z0 < s.z1 ∧ s.z1 ≤ 200 ∧
  node s.j < L ∧ s.j < s.pi ∧ 1 - node s.pi ≤ node s.k ∧ node s.l < L ∧
  L + (1 - node s.pi) / 2 < node s.z0 ∧ 0 ≤ 1 - node s.pi + node s.k - L ∧
  0 ≤ s.x ∧ 0 ≤ s.y ∧ s.z1 = s.z0 + 1 ∧ 200 - s.pi ≤ s.z0 ∧
  s.xDual.objective = s.xObjective ∧ s.yDual.objective = s.yObjective ∧
  s.xDual.bound = 0 ∧ s.yDual.bound = 0

instance (s : MovingStage) : Decidable s.Valid := by unfold Valid; infer_instance

theorem row_of_objective_bounds {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions (L : ℝ) phi)
    (s : MovingStage) (hv : s.Valid)
    (hx : 0 ≤ termsValue (gridValues phi) s.xObjective)
    (hy : 0 ≤ termsValue (gridValues phi) s.yObjective) : RowHolds s.tag (gridValues phi) := by
  rcases hv with ⟨hpi0, hpi1, hij, hkl, hzz, hz1, hjL, hjpi, hpk, hlL, hzL, hkap,
    hx0, hy0, hwidth, hshift, _hxobj, _hyobj, _hxb, _hyb⟩
  have hri : 200 - s.pi ≤ 200 := Nat.sub_le _ _
  have hz0 : s.z0 ≤ 200 := hzz.le.trans hz1
  have hsr1 : s.z1 - (200 - s.pi) ≤ 200 := (Nat.sub_le _ _).trans hz1
  have hsr0 : s.z0 - (200 - s.pi) ≤ 200 := (Nat.sub_le _ _).trans hz0
  have hpiR : (node s.pi : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    simp only [node_cast]
    constructor
    · exact div_pos (by exact_mod_cast hpi0) (by norm_num)
    · have hh : (s.pi : ℝ) < 200 := by exact_mod_cast hpi1
      linarith
  have hp : 1 - (node s.pi : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hpiR.2], by linarith [hpiR.1]⟩
  have hR := h.primitive_pos (1 - (node s.pi : ℝ)) hp
  have hindex : ((200 - s.pi : ℕ) : ℝ) / 200 = 1 - (node s.pi : ℝ) := by
    rw [Nat.cast_sub hpi1.le, node_cast]
    norm_num
    ring
  have hxratio : (s.x : ℝ) ≤ activationPrimitive phi (1 - (1 - (node s.pi : ℝ))) /
      activationPrimitive phi (1 - (node s.pi : ℝ)) := by
    simp only [xObjective, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hx
    rw [termValue_J phi s.pi 1 hpi1.le, termValue_J phi (200 - s.pi) (-s.x) hri] at hx
    simp only [Rat.cast_one, Rat.cast_neg, one_mul, add_zero, hindex] at hx
    rw [le_div_iff₀ hR]
    simp only [sub_sub_cancel, node_cast]
    simp only [node_cast] at hx
    linarith
  have hz0R : 1 - (node s.pi : ℝ) ≤ (node s.z0 : ℝ) := by
    rw [← hindex, node_cast]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hshift) (by norm_num)
  have hzR : (node s.z0 : ℝ) < (node s.z1 : ℝ) := by
    simp only [node_cast]
    exact div_lt_div_of_pos_right (by exact_mod_cast hzz) (by norm_num)
  have hwidthR : (node s.z1 : ℝ) - (node s.z0 : ℝ) = 1 / 200 := by
    simp only [node_cast, hwidth, Nat.cast_add, Nat.cast_one]
    ring
  have hsindex (z : ℕ) (hz : 200 - s.pi ≤ z) :
      ((z - (200 - s.pi) : ℕ) : ℝ) / 200 = (node z : ℝ) - (1 - (node s.pi : ℝ)) := by
    rw [Nat.cast_sub hz, node_cast, ← hindex]
    ring
  have hyratio : (s.y : ℝ) ≤ binAverage
      (fun z => activationPrimitive phi (z - (1 - (node s.pi : ℝ))) - activationPrimitive phi z)
      (node s.z0 : ℝ) (node s.z1 : ℝ) / activationPrimitive phi (1 - (node s.pi : ℝ)) := by
    simp only [yObjective, termsValue, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at hy
    rw [termValue_V phi s.z1 (-200) hz1, termValue_V phi s.z0 200 hz0,
      termValue_V phi (s.z1 - (200 - s.pi)) 200 hsr1,
      termValue_V phi (s.z0 - (200 - s.pi)) (-200) hsr0,
      termValue_J phi (200 - s.pi) (-s.y) hri] at hy
    rw [le_div_iff₀ hR,
      h.toNormalizedNecessaryTwoClass.gap_binAverage_eq hp.1.le hz0R hzR
        (by simpa only [node_cast] using (grid_rank_mem hz1).2), hwidthR]
    rw [hsindex s.z1 (hshift.trans hzz.le), hsindex s.z0 hshift, hindex] at hy
    simp only [Rat.cast_neg, Rat.cast_ofNat, add_zero] at hy
    simp only [node_cast] at hy ⊢
    nlinarith
  exact moving_row h hpi0 hpi1 hij hkl hzz hz1 hjL hjpi hpk hlL hzL hkap hx0 hy0 hxratio hyratio

/-- Checked x/y dual certificates use only previously established rows and
produce this stage's actual moving row. -/
theorem sound {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions (L : ℝ) phi)
    (s : MovingStage) (hv : s.Valid) {rows : Array RowTag} {terms : Array Terms} {rhs : Array ℚ} {known : ℕ}
    (hcache : DualProposal.checkRowCache rows terms rhs = true)
    (hxc : s.xDual.checkCached rows terms rhs known = true)
    (hyc : s.yDual.checkCached rows terms rhs known = true)
    (hknown : ∀ i < known, RowHolds rows[i]! (gridValues phi)) :
    RowHolds s.tag (gridValues phi) := by
  have hx := DualProposal.checkCached_sound hcache hxc (gridValues phi) hknown
    (gridValues_lower h.toNormalizedNecessaryTwoClass) (gridValues_upper h.toNormalizedNecessaryTwoClass)
  have hy := DualProposal.checkCached_sound hcache hyc (gridValues phi) hknown
    (gridValues_lower h.toNormalizedNecessaryTwoClass) (gridValues_upper h.toNormalizedNecessaryTwoClass)
  have hvalid := hv
  rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hxobj, hyobj, hxb, hyb⟩
  rw [coeff_value, hxobj, hxb, Rat.cast_zero] at hx
  rw [coeff_value, hyobj, hyb, Rat.cast_zero] at hy
  exact row_of_objective_bounds h s hvalid hx hy

end MovingStage
end OptimalG.UniversalLP
