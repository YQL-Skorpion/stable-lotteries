import OptimalG.VariationalRankMatching
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! A genuine continuous implicit branch on a compact interval, constructed
by the intermediate value theorem and a quantitative monotonicity bound. -/
namespace OptimalG
open Set Filter
open scoped Topology NNReal

/-- Lower increments control the inverse distance without an inverse assumption. -/
theorem inverse_distance_of_lower_increment {F : ℝ → ℝ} {a b m x y : ℝ}
    (hm : 0 < m)
    (hgrowth : ∀ u ∈ Icc a b,∀ v ∈ Icc a b,u ≤ v → m*(v-u) ≤ F v-F u)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    m*dist x y ≤ dist (F x) (F y) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this hy hx (le_of_not_ge hxy)
  have hi := hgrowth x hx y hy hxy
  have hf : F x ≤ F y := by nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hxy)]
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy),
    abs_of_nonpos (sub_nonpos.mpr hf)]
  nlinarith only [hi]

/-- Quantitative growth also identifies every solution of a given level. -/
theorem eq_of_lower_increment {F : ℝ → ℝ} {a b m x y : ℝ}
    (hm : 0<m)
    (hgrowth : ∀ u ∈ Icc a b,∀ v ∈ Icc a b,u≤v → m*(v-u)≤F v-F u)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hlevel : F x=F y) : x=y := by
  have hh := inverse_distance_of_lower_increment hm hgrowth hx hy
  rw [hlevel,dist_self] at hh
  have hmzero : m*dist x y=0 := le_antisymm hh (mul_nonneg hm.le dist_nonneg)
  exact dist_eq_zero.mp ((mul_eq_zero.mp hmzero).resolve_left hm.ne')

/-- Every level in the image has a branch, and that branch is Lipschitz. -/
theorem exists_lipschitz_implicit_curve {F G : ℝ → ℝ} {a b c d m : ℝ} {K : ℝ≥0}
    (hab : a ≤ b) (hm : 0 < m) (hF : ContinuousOn F (Icc a b))
    (hgrowth : ∀ u ∈ Icc a b,∀ v ∈ Icc a b,u ≤ v → m*(v-u) ≤ F v-F u)
    (hG : LipschitzOnWith K G (Icc c d))
    (hrange : ∀ t ∈ Icc c d,G t ∈ Icc (F a) (F b)) :
    ∃ q : ℝ → ℝ,(∀ t ∈ Icc c d,q t ∈ Icc a b ∧ F (q t)=G t) ∧
      LipschitzOnWith (K/⟨m,hm.le⟩) q (Icc c d) := by
  have hex : ∀ t ∈ Icc c d,∃ u ∈ Icc a b,F u=G t := by
    intro t ht
    exact intermediate_value_Icc hab hF (hrange t ht)
  classical
  let q : ℝ → ℝ := fun t => if ht : t ∈ Icc c d then (hex t ht).choose else a
  have hq : ∀ t ∈ Icc c d,q t ∈ Icc a b ∧ F (q t)=G t := by
    intro t ht
    simpa only [q,dif_pos ht] using (hex t ht).choose_spec
  refine ⟨q,hq,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hinv := inverse_distance_of_lower_increment hm hgrowth (hq x hx).1 (hq y hy).1
  rw [(hq x hx).2,(hq y hy).2] at hinv
  have hh := hinv.trans (hG.dist_le_mul x hx y hy)
  change dist (q x) (q y) ≤ ((K:ℝ)/m)*dist x y
  have he : ((K:ℝ)/m)*dist x y=((K:ℝ)*dist x y)/m := by ring
  rw [he]
  exact (le_div_iff₀ hm).mpr (by nlinarith only [hh])

/-- Differentiability follows from the actual matching equation and the
nonzero derivative of F; no differentiability of the branch is assumed. -/
theorem implicit_curve_hasDerivAt {F G q : ℝ → ℝ} {c d t f' g' : ℝ}
    (ht : t ∈ Ioo c d) (hq : ContinuousOn q (Icc c d))
    (hmatch : ∀ u ∈ Icc c d,F (q u)=G u)
    (hF : HasDerivAt F f' (q t)) (hG : HasDerivAt G g' t) (hf : f' ≠ 0) :
    HasDerivAt q (g'/f') t := by
  apply HasDerivAt.of_comp_left (hq.continuousAt (Icc_mem_nhds ht.1 ht.2)) hF hG hf
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
  exact hmatch u hu

end OptimalG
