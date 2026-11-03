import OptimalG.ScoreResidual
import OptimalG.RationalImplicit

/-!
# Exact rational voter weights near a regular stationary profile

The implicit equation is the actual centered candidate-score vector. A rational
probability vector is realized by natural voter multiplicities; the corrected
lottery remains positive, has total mass one, and is exactly stable. Any given
open neighborhood in voter weights and lottery masses can be preserved.
-/

namespace OptimalG
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem tangentLottery_total {m : ℕ} [NeZero m] (h : probabilityTangent (Fin m)) :
    ∑ a, tangentLottery h a = 1 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hs : ∑ a, h.val a = 0 := h.property
  simp [tangentLottery, uniformVector, Finset.sum_add_distrib, hs, hm]

theorem tangentLottery_continuous {m : ℕ} :
    Continuous (tangentLottery (m := m)) := by
  exact continuous_const.add continuous_subtype_val

/-- Equal scores at a probability lottery have the exact common value τ. -/
theorem common_scores_equal_mean {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1))
    (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (D : Lottery m)
    (hwsum : ∑ v, w v = 1)
    (hcommon : ∀ a b, expectation w (fun v => orderedActivation g D.weight (orders v) a) =
      expectation w (fun v => orderedActivation g D.weight (orders v) b)) :
    ∀ a, expectation w (fun v => orderedActivation g D.weight (orders v) a) = ∫ r in (0 : ℝ)..1, g r := by
  intro a
  have hpart : expectation D.weight (fun b => expectation w
      (fun v => orderedActivation g D.weight (orders v) b)) = ∫ r in (0 : ℝ)..1, g r := by
    rw [expectation_commute]
    simp_rw [ordered_integral_partition g D.weight _ hg D.nonneg D.total]
    exact expectation_const hwsum _
  have heq : expectation D.weight (fun b => expectation w
      (fun v => orderedActivation g D.weight (orders v) b)) =
      expectation w (fun v => orderedActivation g D.weight (orders v) a) := by
    simp_rw [hcommon _ a]
    exact expectation_const D.total _
  exact heq.symm.trans hpart

/-- The full-support regular realization theorem. It preserves an arbitrary
neighborhood, so strict cost inequalities survive without approximate stability. -/
theorem exists_rational_stationary_near_regular {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m))
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hwsum : ∑ v, w v = 1) (mean : ℝ)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (uniformVector m)) = mean)
    (hregular : ∀ h : Fin m → ℝ, (∑ a, h a) = 0 →
      profileLotteryJacobian g orders w (uniformVector m) h = 0 → h = 0)
    (U : Set ((V → ℝ) × (Fin m → ℝ))) (hU : U ∈ 𝓝 (w, uniformVector m)) :
    ∃ copies : V → ℕ, ∃ hcopies : 0 < ∑ v, copies v, ∃ D : Lottery m,
      (∀ a, 0 < D.weight a) ∧ (copyWeight copies, D.weight) ∈ U ∧
      ∀ a, expectation (copyWeight copies) (fun v => orderedActivation g D.weight (orders v) a) =
        ∫ r in (0 : ℝ)..1, g r := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hu : (1 / (m : ℝ)) ≠ 0 := ne_of_gt (div_pos (by norm_num) hmpos)
  have hderiv := scoreResidual_hasStrictFDerivAt g hg orders w
  have hinv : ((scoreResidualDerivative g orders w).comp
      (ContinuousLinearMap.inr ℝ (V → ℝ) (probabilityTangent (Fin m)))).IsInvertible := by
    rw [scoreResidual_partialDerivative g orders w mean hu hstationary]
    exact profileTangentJacobian_isInvertible g orders w (1 / (m : ℝ)) mean hu hstationary hregular
  have hcontinuous : Continuous (fun p : (V → ℝ) × probabilityTangent (Fin m) => (p.1, tangentLottery p.2)) :=
    continuous_fst.prodMk (tangentLottery_continuous.comp continuous_snd)
  have hnear : ∀ᶠ p : (V → ℝ) × probabilityTangent (Fin m) in 𝓝 (w, 0),
      (p.1, tangentLottery p.2) ∈ U := by
    have hh := hcontinuous.continuousAt.tendsto.eventually
      (show U ∈ 𝓝 ((w, (0 : probabilityTangent (Fin m))).1, tangentLottery (0 : probabilityTangent (Fin m))) by
        simpa [tangentLottery] using hU)
    exact hh
  have hpositive : ∀ᶠ p : (V → ℝ) × probabilityTangent (Fin m) in 𝓝 (w, 0),
      ∀ a, 0 < tangentLottery p.2 a := by
    apply eventually_all.mpr
    intro a
    have ht : Tendsto (fun p : (V → ℝ) × probabilityTangent (Fin m) => tangentLottery p.2 a)
        (𝓝 (w, 0)) (𝓝 (1 / (m : ℝ))) := by
      have hc : Continuous (fun p : (V → ℝ) × probabilityTangent (Fin m) => tangentLottery p.2 a) :=
        (continuous_apply a).comp (tangentLottery_continuous.comp continuous_snd)
      simpa [tangentLottery, uniformVector] using hc.continuousAt.tendsto (x := (w, 0))
    exact ht.eventually_const_lt (div_pos (by norm_num) hmpos)
  obtain ⟨copies, hcopies, h, hmem, hscore⟩ := exists_rational_parameter_implicit
    (scoreResidual g orders) (scoreResidualDerivative g orders w) w (0 : probabilityTangent (Fin m))
    hw hwsum hderiv hinv
    {p | (p.1, tangentLottery p.2) ∈ U ∧ ∀ a, 0 < tangentLottery p.2 a} (hnear.and hpositive)
  let D : Lottery m := ⟨tangentLottery h, fun a => (hmem.2 a).le, tangentLottery_total h⟩
  have hzero : scoreResidual g orders (copyWeight copies, h) = 0 :=
    hscore.trans (scoreResidual_at_stationary g orders w mean hstationary)
  have hcommon := (probabilityProjection_eq_zero_iff _).mp hzero
  refine ⟨copies, hcopies, D, hmem.2, hmem.1, ?_⟩
  apply common_scores_equal_mean g hg.continuousOn orders (copyWeight copies) D (copyWeight_total copies hcopies)
  intro a b
  have heq := hcommon a b
  change expectation (copyWeight copies) (fun v => scoreExtension g (orders v) a D.weight) =
    expectation (copyWeight copies) (fun v => scoreExtension g (orders v) b D.weight) at heq
  simpa only [scoreExtension_eq_orderedActivation g hg _ a D.weight (ne_of_gt (hmem.2 a)),
    scoreExtension_eq_orderedActivation g hg _ b D.weight (ne_of_gt (hmem.2 b))] using heq

end OptimalG
