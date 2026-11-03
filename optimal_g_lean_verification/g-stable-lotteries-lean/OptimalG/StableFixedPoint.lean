import OptimalG.External.FixedPointTheorems.brouwer
import Mathlib.Analysis.Convex.StdSimplex
import OptimalG.Finite

/-! # A continuous score partition has a stable lottery

The fixed-point theorem is supplied by the pinned, fully proved cubical Sperner
development in `External/FixedPointTheorems`; no fixed-point axiom is used.
-/

namespace OptimalG
open Set
open scoped BigOperators

/-- A continuous finite score map whose lottery-weighted mean is fixed admits
a lottery at which every candidate score is at most that mean. -/
theorem exists_simplex_score_bound {m : ℕ} [NeZero m]
    (score : (Fin m → ℝ) → Fin m → ℝ) (mean : ℝ)
    (hcont : ∀ a, ContinuousOn (fun D => score D a) (stdSimplex ℝ (Fin m)))
    (hpartition : ∀ D ∈ stdSimplex ℝ (Fin m), expectation D (score D) = mean) :
    ∃ D ∈ stdSimplex ℝ (Fin m), ∀ a, score D a ≤ mean := by
  classical
  let K := stdSimplex ℝ (Fin m)
  let delta := fun (D : K) a => max 0 (score D.val a - mean)
  let total := fun D : K => ∑ a, delta D a
  have hdelta : ∀ D a, 0 ≤ delta D a := fun D a => le_max_left _ _
  have htotal : ∀ D, 0 ≤ total D := fun D => Finset.sum_nonneg (fun a _ => hdelta D a)
  have hden : ∀ D, 0 < 1 + total D := fun D => by linarith [htotal D]
  have hcDelta : ∀ a, Continuous (fun D : K => delta D a) := by
    intro a
    exact continuous_const.max ((hcont a).restrict.sub continuous_const)
  have hcTotal : Continuous total := continuous_finsetSum _ (fun a _ => hcDelta a)
  let next := fun (D : K) a => (D.val a + delta D a) / (1 + total D)
  have hnext : ∀ D, next D ∈ K := by
    intro D
    constructor
    · intro a
      exact div_nonneg (add_nonneg (D.property.1 a) (hdelta D a)) (hden D).le
    · dsimp [next]
      rw [← Finset.sum_div, Finset.sum_add_distrib, D.property.2]
      exact div_self (ne_of_gt (hden D))
  have hcNext : Continuous next := by
    apply continuous_pi
    intro a
    exact (((continuous_apply a).comp continuous_subtype_val).add (hcDelta a)).div
      (continuous_const.add hcTotal) (fun D => ne_of_gt (hden D))
  let F : C(K, K) := ⟨fun D => ⟨next D, hnext D⟩, hcNext.subtype_mk hnext⟩
  have hne : K.Nonempty := ⟨Pi.single (0 : Fin m) 1, single_mem_stdSimplex ℝ 0⟩
  obtain ⟨D, hfixed⟩ := brouwer_fixed_point K (convex_stdSimplex ℝ (Fin m))
    (isCompact_stdSimplex ℝ (Fin m)) hne F
  have hfix (a : Fin m) : delta D a = D.val a * total D := by
    have he := congrArg (fun Q : K => Q.val a) hfixed
    change (D.val a + delta D a) / (1 + total D) = D.val a at he
    have hm := (div_eq_iff (ne_of_gt (hden D))).mp he
    nlinarith only [hm]
  refine ⟨D.val, D.property, ?_⟩
  intro a
  by_contra! ha
  have hda : 0 < delta D a := lt_of_lt_of_le (sub_pos.mpr ha) (le_max_right _ _)
  have hSa : delta D a ≤ total D := Finset.single_le_sum (fun i _ => hdelta D i) (Finset.mem_univ a)
  have hS : 0 < total D := hda.trans_le hSa
  have hpositive (i : Fin m) (hi : 0 < D.val i) : 0 < score D.val i - mean := by
    have hd : 0 < delta D i := by rw [hfix]; exact mul_pos hi hS
    exact (lt_max_iff.mp hd).resolve_left (lt_irrefl (0 : ℝ))
  have hterms : ∀ i : Fin m, 0 ≤ D.val i * (score D.val i - mean) := by
    intro i
    by_cases hi : D.val i = 0
    · simp [hi]
    · exact (mul_pos (lt_of_le_of_ne (D.property.1 i) (Ne.symm hi))
        (hpositive i (lt_of_le_of_ne (D.property.1 i) (Ne.symm hi)))).le
  have hDa : 0 < D.val a := by
    by_contra! hn
    have hzero : D.val a = 0 := le_antisymm hn (D.property.1 a)
    rw [hfix, hzero, zero_mul] at hda
    exact (lt_irrefl 0) hda
  have hsumPos : 0 < ∑ i, D.val i * (score D.val i - mean) :=
    Finset.sum_pos' (fun i _ => hterms i) ⟨a, Finset.mem_univ a, mul_pos hDa (sub_pos.mpr ha)⟩
  have hzero : (∑ i, D.val i * (score D.val i - mean)) = 0 := by
    rw [show (∑ i, D.val i * (score D.val i - mean)) =
        expectation D.val (score D.val) - (∑ i, D.val i) * mean by
      simp only [expectation, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]]
    rw [hpartition D.val D.property, D.property.2]
    ring
  rw [hzero] at hsumPos
  exact (lt_irrefl 0) hsumPos

end OptimalG
