import OptimalG.ScoreTangent

/-! # The actual score equation used in the implicit-function theorem -/

namespace OptimalG
open scoped BigOperators

noncomputable def uniformVector (m : ℕ) : Fin m → ℝ := fun _ => 1 / (m : ℝ)

noncomputable def tangentLottery {m : ℕ} (h : probabilityTangent (Fin m)) : Fin m → ℝ :=
  uniformVector m + h.val

noncomputable def scoreInputLinear (V : Type*) [Fintype V] (m : ℕ) :
    ((V → ℝ) × probabilityTangent (Fin m)) →L[ℝ] ((V → ℝ) × (Fin m → ℝ)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((probabilityTangent (Fin m)).subtypeL.comp (ContinuousLinearMap.snd ℝ _ _))

noncomputable def scoreResidual {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m))
    (p : (V → ℝ) × probabilityTangent (Fin m)) : probabilityTangent (Fin m) :=
  probabilityProjection (fun a => weightedScoreExtension g orders a (p.1, tangentLottery p.2))

noncomputable def scoreResidualDerivative {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) :
    ((V → ℝ) × probabilityTangent (Fin m)) →L[ℝ] probabilityTangent (Fin m) :=
  probabilityProjectionContinuous.comp
    ((ContinuousLinearMap.pi (fun a => weightedScoreDerivative g orders a (w, uniformVector m))).comp
      (scoreInputLinear V m))

theorem scoreResidual_hasStrictFDerivAt {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (hg : Continuous g) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) :
    HasStrictFDerivAt (scoreResidual g orders) (scoreResidualDerivative g orders w) (w, 0) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hinput : HasStrictFDerivAt
      (fun p : (V → ℝ) × probabilityTangent (Fin m) => (p.1, tangentLottery p.2))
      (scoreInputLinear V m) (w, 0) := by
    convert! (scoreInputLinear V m).hasStrictFDerivAt.add_const ((0 : V → ℝ), uniformVector m) using 1
    funext p
    simp [scoreInputLinear, tangentLottery, add_comm]
  have hscore : HasStrictFDerivAt (fun p : (V → ℝ) × (Fin m → ℝ) =>
      fun a => weightedScoreExtension g orders a p)
      (ContinuousLinearMap.pi (fun a => weightedScoreDerivative g orders a (w, uniformVector m)))
      (w, uniformVector m) := by
    apply hasStrictFDerivAt_pi.mpr
    intro a
    exact weightedScoreExtension_hasStrictFDerivAt g hg orders a _ (one_div_ne_zero hm)
  have hscore' : HasStrictFDerivAt (fun p : (V → ℝ) × (Fin m → ℝ) =>
      fun a => weightedScoreExtension g orders a p)
      (ContinuousLinearMap.pi (fun a => weightedScoreDerivative g orders a (w, uniformVector m)))
      (w, tangentLottery (0 : probabilityTangent (Fin m))) := by
    simpa only [tangentLottery, Submodule.coe_zero, add_zero] using hscore
  have hcomp := hscore'.comp (w, 0) hinput
  exact probabilityProjectionContinuous.hasStrictFDerivAt.comp (w, 0) hcomp

theorem scoreResidual_at_stationary {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (mean : ℝ)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (uniformVector m)) = mean) :
    scoreResidual g orders (w, 0) = 0 := by
  apply (probabilityProjection_eq_zero_iff _).mpr
  intro a b
  change expectation w (fun v => scoreExtension g (orders v) a (uniformVector m + (0 : probabilityTangent (Fin m)).val)) = _
  simpa only [Submodule.coe_zero, add_zero, weightedScoreExtension, tangentLottery] using
    (hstationary a).trans (hstationary b).symm

/-- The partial lottery derivative of the residual equation is the actual
stationary Jacobian restricted to the simplex tangent. -/
theorem scoreResidual_partialDerivative {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (mean : ℝ)
    (hu : (1 / (m : ℝ)) ≠ 0)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (uniformVector m)) = mean) :
    (scoreResidualDerivative g orders w).comp (ContinuousLinearMap.inr ℝ (V → ℝ) (probabilityTangent (Fin m))) =
      (profileTangentJacobian g orders w (1 / (m : ℝ)) mean hu hstationary).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro h
  have hvec : (ContinuousLinearMap.pi (fun a => weightedScoreDerivative g orders a (w, uniformVector m)))
      (scoreInputLinear V m (0, h)) = profileLotteryJacobian g orders w (uniformVector m) h.val := by
    ext a
    simp [scoreInputLinear, weightedScoreDerivative, profileLotteryJacobian]
  change probabilityProjection ((ContinuousLinearMap.pi
    (fun a => weightedScoreDerivative g orders a (w, uniformVector m)))
      (scoreInputLinear V m (0, h))) = _
  rw [hvec]
  exact probabilityProjection_tangent (profileTangentJacobian g orders w (1 / (m : ℝ)) mean hu hstationary h)

end OptimalG
