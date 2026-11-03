import OptimalG.RankIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The actual derivative of candidate activation

For positive candidate mass, the rank-interval average is the quotient of two
primitive values by the candidate mass. Its strict Fréchet derivative is proved
from the fundamental theorem of calculus. This supplies the analytic map used
in the equal-voter realization argument.
-/

namespace OptimalG
open Set MeasureTheory
open scoped BigOperators Topology

/-- The linear map giving the lottery mass below a candidate in a fixed order. -/
noncomputable def rankPrefixLinear {m : ℕ} (order : Equiv.Perm (Fin m)) (a : Fin m) :
    (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin m, if i.val < (order.symm a).val then ContinuousLinearMap.proj (order i) else 0

theorem rankPrefixLinear_apply {m : ℕ} (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) :
    rankPrefixLinear order a D = rankCut (fun i => D (order i)) (order.symm a).val := by
  simp only [rankPrefixLinear, sum_apply, rankCut]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

noncomputable def activationPrimitive (g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ x in (0 : ℝ)..r, g x

/-- A globally defined smooth extension of the positive-mass interval average. -/
noncomputable def scoreExtension {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) : ℝ :=
  (activationPrimitive g (rankPrefixLinear order a D + D a) -
    activationPrimitive g (rankPrefixLinear order a D)) / D a

/-- At positive masses the extension equals the actual activation definition. -/
theorem scoreExtension_eq_orderedActivation {m : ℕ} (g : ℝ → ℝ)
    (hg : Continuous g) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hDa : D a ≠ 0) :
    scoreExtension g order a D = orderedActivation g D order a := by
  have hint := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 (rankPrefixLinear order a D))
    (hg.intervalIntegrable (rankPrefixLinear order a D) (rankPrefixLinear order a D + D a))
  have hmass := mass_mul_rankActivation g (fun i => D (order i)) (order.symm a)
  rw [rankCut_succ] at hmass
  simp only [Equiv.apply_symm_apply] at hmass
  rw [← rankPrefixLinear_apply] at hmass
  unfold scoreExtension activationPrimitive orderedActivation
  apply (div_eq_iff hDa).mpr
  linarith

/-- Explicit derivative, written in the product-rule form. -/
noncomputable def scoreDerivative {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] ℝ :=
  let L := rankPrefixLinear order a
  let P : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
  (activationPrimitive g (L D + D a) - activationPrimitive g (L D)) •
      (-(D a ^ 2)⁻¹ • P) +
    (D a)⁻¹ • (g (L D + D a) • (L + P) - g (L D) • L)

theorem scoreExtension_hasStrictFDerivAt {m : ℕ} (g : ℝ → ℝ)
    (hg : Continuous g) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hDa : D a ≠ 0) :
    HasStrictFDerivAt (scoreExtension g order a) (scoreDerivative g order a D) D := by
  let L := rankPrefixLinear order a
  let P : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj a
  have hL := L.hasStrictFDerivAt (x := D)
  have hP := P.hasStrictFDerivAt (x := D)
  have hright := (hg.integral_hasStrictDerivAt 0 (L D + D a)).comp_hasStrictFDerivAt D (hL.add hP)
  have hleft := (hg.integral_hasStrictDerivAt 0 (L D)).comp_hasStrictFDerivAt D hL
  have hinv := (hasStrictDerivAt_inv hDa).comp_hasStrictFDerivAt D hP
  convert! (hright.sub hleft).mul hinv using 1

/-- The pointwise differential formula used to calculate the auxiliary profile. -/
theorem scoreDerivative_apply {m : ℕ} (g : ℝ → ℝ) (order : Equiv.Perm (Fin m))
    (a : Fin m) (D h : Fin m → ℝ) (hDa : D a ≠ 0) :
    scoreDerivative g order a D h =
      (g (rankPrefixLinear order a D + D a) * (rankPrefixLinear order a h + h a) -
       g (rankPrefixLinear order a D) * rankPrefixLinear order a h -
       scoreExtension g order a D * h a) / D a := by
  simp only [scoreDerivative, scoreExtension, add_apply,
    sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  field_simp
  ring

/-- Extend an activation continuously by its endpoint values. -/
noncomputable def clippedActivation (g : ℝ → ℝ) (r : ℝ) : ℝ := g (max 0 (min 1 r))

theorem clippedActivation_eq (g : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 1) :
    clippedActivation g r = g r := by
  simp [clippedActivation, min_eq_right hr.2, max_eq_right hr.1]

theorem clippedActivation_continuous (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    Continuous (clippedActivation g) := by
  apply continuousOn_univ.mp
  exact hg.comp ((continuous_const.max (continuous_const.min continuous_id)).continuousOn)
    (fun r _ => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)

/-- Clipping leaves every lottery rank-interval activation unchanged. -/
theorem rankActivation_clipped {m : ℕ} (g : ℝ → ℝ) (D : Fin m → ℝ)
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (a : Fin m) :
    rankActivation (clippedActivation g) D a = rankActivation g D a := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hu
  apply clippedActivation_eq
  have hleft := rankCut_mem_Icc D hD hsum a.val
  have hright := rankCut_mem_Icc D hD hsum (a.val + 1)
  rw [rankCut_succ] at hright
  constructor
  · exact add_nonneg hleft.1 (mul_nonneg hu.1 (hD a))
  · have hmul := mul_le_of_le_one_left (hD a) hu.2
    linarith [hright.2]

theorem orderedActivation_clipped {m : ℕ} (g : ℝ → ℝ) (D : Fin m → ℝ)
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1)
    (order : Equiv.Perm (Fin m)) (a : Fin m) :
    orderedActivation (clippedActivation g) D order a = orderedActivation g D order a := by
  apply rankActivation_clipped g (fun i => D (order i)) (fun i => hD (order i))
  simpa only [Equiv.sum_comp] using hsum

/-- Positive-mass actual scores are represented by the globally differentiable
extension, even when g was only assumed continuous on the rank interval. -/
theorem clipped_scoreExtension_eq_orderedActivation {m : ℕ} (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1)) (order : Equiv.Perm (Fin m)) (a : Fin m)
    (D : Fin m → ℝ) (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (hDa : D a ≠ 0) :
    scoreExtension (clippedActivation g) order a D = orderedActivation g D order a := by
  rw [scoreExtension_eq_orderedActivation _ (clippedActivation_continuous g hg) order a D hDa,
    orderedActivation_clipped g D hD hsum]

/-- The actual finite weighted profile score, extended to a neighborhood in
voter probabilities and positive candidate masses. -/
noncomputable def weightedScoreExtension {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) : ℝ :=
  expectation p.1 (fun v => scoreExtension g (orders v) a p.2)

noncomputable def weightedScoreDerivative {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) : ((V → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ :=
  ∑ v, (p.1 v • ((scoreDerivative g (orders v) a p.2).comp (ContinuousLinearMap.snd ℝ _ _)) +
    scoreExtension g (orders v) a p.2 •
      ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ _ _)))

/-- Strict differentiability in voter weights and candidate masses jointly. -/
theorem weightedScoreExtension_hasStrictFDerivAt {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m)) (a : Fin m)
    (p : (V → ℝ) × (Fin m → ℝ)) (hDa : p.2 a ≠ 0) :
    HasStrictFDerivAt (weightedScoreExtension g orders a) (weightedScoreDerivative g orders a p) p := by
  have hterm (v : V) : HasStrictFDerivAt
      (fun q : (V → ℝ) × (Fin m → ℝ) => q.1 v * scoreExtension g (orders v) a q.2)
      (p.1 v • ((scoreDerivative g (orders v) a p.2).comp (ContinuousLinearMap.snd ℝ _ _)) +
       scoreExtension g (orders v) a p.2 •
         ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ _ _))) p := by
    have hproj := ((ContinuousLinearMap.proj v).comp (ContinuousLinearMap.fst ℝ (V → ℝ) (Fin m → ℝ))).hasStrictFDerivAt (x := p)
    have hs := (scoreExtension_hasStrictFDerivAt g hg (orders v) a p.2 hDa).comp p
      ((ContinuousLinearMap.snd ℝ (V → ℝ) (Fin m → ℝ)).hasStrictFDerivAt (x := p))
    convert! hproj.mul hs using 1
  exact HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun v _ => hterm v)

theorem weightedScoreExtension_eq {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (orders : V → Equiv.Perm (Fin m)) (a : Fin m) (w : V → ℝ)
    (D : Fin m → ℝ) (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) (hDa : D a ≠ 0) :
    weightedScoreExtension (clippedActivation g) orders a (w, D) =
      expectation w (fun v => orderedActivation g D (orders v) a) := by
  unfold weightedScoreExtension expectation
  apply Finset.sum_congr rfl
  intro v _
  change w v * scoreExtension (clippedActivation g) (orders v) a D = _
  rw [clipped_scoreExtension_eq_orderedActivation g hg (orders v) a D hD hsum hDa]

end OptimalG
