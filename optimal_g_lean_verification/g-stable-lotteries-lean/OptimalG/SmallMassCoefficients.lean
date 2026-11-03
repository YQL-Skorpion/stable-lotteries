import OptimalG.SmallMassCurveTransport

/-! The concrete C.21 coefficient families and their ordinary derivatives. -/
namespace OptimalG
open Set

noncomputable def smallMassDenominator (J : ℝ → ℝ) (lam S p : ℝ) : ℝ :=
  J p+Variational.quadratic lam (1-p)-S
noncomputable def smallMassBeta (J : ℝ → ℝ) (lam S p : ℝ) : ℝ :=
  (lam+p)/smallMassDenominator J lam S p
noncomputable def smallMassTarget (J : ℝ → ℝ) (lam S p : ℝ) : ℝ :=
  lam-p+smallMassBeta J lam S p*J p
noncomputable def smallMassBetaDerivative (J phi : ℝ → ℝ) (lam S p : ℝ) : ℝ :=
  (smallMassDenominator J lam S p-(lam+p)*(phi p+1-p-lam))/
    (smallMassDenominator J lam S p)^2
noncomputable def smallMassTargetDerivative (J phi : ℝ → ℝ) (lam S p : ℝ) : ℝ :=
  -1+smallMassBetaDerivative J phi lam S p*J p+smallMassBeta J lam S p*phi p

theorem smallMassTarget_identity {J : ℝ → ℝ} {lam S p : ℝ}
    (hD : smallMassDenominator J lam S p≠0) :
    smallMassTarget J lam S p=2*lam-smallMassBeta J lam S p*(Variational.quadratic lam (1-p)-S) := by
  unfold smallMassTarget smallMassBeta
  have he := div_mul_cancel₀ (lam+p) hD
  dsimp [smallMassDenominator] at he
  dsimp [smallMassDenominator]
  nlinarith only [he]

theorem smallMassBeta_hasDerivAt {J phi : ℝ → ℝ} {lam S p : ℝ}
    (hJ : HasDerivAt J (phi p) p) (hD : smallMassDenominator J lam S p≠0) :
    HasDerivAt (smallMassBeta J lam S) (smallMassBetaDerivative J phi lam S p) p := by
  have hQ := (Variational.quadratic_hasDerivAt lam (1-p)).comp p
    ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p))
  have hden := (hJ.add hQ).sub_const S
  have hnum := (hasDerivAt_id p).const_add lam
  have hh := hnum.div hden hD
  convert! hh using 1 <;>
    (try dsimp [smallMassBeta,smallMassBetaDerivative,smallMassDenominator,Function.comp_def]) <;>
    first | rfl | ring

theorem smallMassTarget_hasDerivAt {J phi : ℝ → ℝ} {lam S p : ℝ}
    (hJ : HasDerivAt J (phi p) p) (hD : smallMassDenominator J lam S p≠0) :
    HasDerivAt (smallMassTarget J lam S) (smallMassTargetDerivative J phi lam S p) p := by
  have hh := ((hasDerivAt_const p lam).sub (hasDerivAt_id p)).add
    ((smallMassBeta_hasDerivAt hJ hD).mul hJ)
  convert! hh using 1 <;>
    (try dsimp [smallMassTarget,smallMassTargetDerivative]) <;> first | rfl | ring

theorem smallMassBeta_continuousOn {J : ℝ → ℝ} {lam S : ℝ} {D : Set ℝ}
    (hc : ContinuousOn J D) (hD : ∀ p ∈ D,smallMassDenominator J lam S p≠0) :
    ContinuousOn (smallMassBeta J lam S) D := by
  have hQ : Continuous (fun p : ℝ => Variational.quadratic lam (1-p)) := by
    unfold Variational.quadratic; fun_prop
  have hden : ContinuousOn (smallMassDenominator J lam S) D :=
    (hc.add hQ.continuousOn).sub continuousOn_const
  exact (continuousOn_const.add continuousOn_id).div hden hD

theorem smallMassTarget_continuousOn {J : ℝ → ℝ} {lam S : ℝ} {D : Set ℝ}
    (hc : ContinuousOn J D) (hD : ∀ p ∈ D,smallMassDenominator J lam S p≠0) :
    ContinuousOn (smallMassTarget J lam S) D :=
  (continuousOn_const.sub continuousOn_id).add ((smallMassBeta_continuousOn hc hD).mul hc)

/-- The numerical negative-target-derivative check supplies the monotonicity
premise of the finite supporting-infimum transport. -/
theorem smallMassTarget_antitone {J phi : ℝ → ℝ} {lam S left right : ℝ}
    (hc : ContinuousOn J (Icc left right))
    (hJ : ∀ p ∈ Ioo left right,HasDerivAt J (phi p) p)
    (hD : ∀ p ∈ Icc left right,smallMassDenominator J lam S p≠0)
    (hd : ∀ p ∈ Ioo left right,smallMassTargetDerivative J phi lam S p≤0) :
    AntitoneOn (smallMassTarget J lam S) (Icc left right) := by
  have hcont := smallMassTarget_continuousOn hc hD
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc left right) hcont
    (f':=smallMassTargetDerivative J phi lam S)
  · intro p hp
    have hp' : p ∈ Ioo left right := by simpa using hp
    exact (smallMassTarget_hasDerivAt (hJ p hp') (hD p ⟨hp'.1.le,hp'.2.le⟩)).hasDerivWithinAt
  · intro p hp
    exact hd p (by simpa using hp)

end OptimalG
