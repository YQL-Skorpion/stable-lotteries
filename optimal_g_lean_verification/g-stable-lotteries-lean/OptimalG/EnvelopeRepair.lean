import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Two corrections required by the manuscript

The last sentence of Appendix A.2 (printed page 21) claims
`φ(0) ≥ -φ(1)/λ`.  For `0 < λ < 1`, this contradicts the already asserted
`φ(0) ≤ λ` and `φ(1) ≤ -1`.  The first theorem checks that incompatibility.
It is a contradiction between these proof claims, not a disproof of the main theorem.

Appendix B.1, Step 2 (printed page 27) reverses the comparison obtained by
integrating `J' ≤ Q'` backwards from a matching endpoint.  We prove the correct
comparison, then verify a sufficient repair of the required endpoint condition
for its running-maximum envelope.  The analytic bounds on the primitive and the
slack bound from Lemma D.1 remain explicit assumptions of the repair.
-/

namespace OptimalG
namespace ManuscriptCorrections

/-- The final bound claimed in A.2 is incompatible with its other bounds
throughout the parameter interval used by the manuscript. -/
theorem a2_endpoint_claim_incompatible (lam phiZero phiOne : ℝ)
    (hlam : 0 < lam) (hlamOne : lam < 1)
    (hzero : phiZero ≤ lam) (hone : phiOne ≤ -1)
    (hclaim : -phiOne / lam ≤ phiZero) : False := by
  have hprod := (div_le_iff₀ hlam).mp hclaim
  have hupper := mul_le_mul_of_nonneg_left hzero (le_of_lt hlam)
  have hgap := mul_pos hlam (sub_pos.mpr hlamOne)
  nlinarith

/-- Actual differentiation for a direct counterexample to A.2's limit inference. -/
theorem a2_example_derivative (r : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 * (1 - t)) (2 * r - 3 * r ^ 2) r := by
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hm : HasDerivAt (fun t : ℝ => 1 - t) (-1) r := by
    exact (hasDerivAt_id r).const_sub 1
  have h := hp.mul hm
  have hd : 2 * r * (1 - r) + r ^ 2 * (-1) = 2 * r - 3 * r ^ 2 := by ring
  change HasDerivAt (fun t : ℝ => t ^ 2 * (1 - t))
    (2 * r * (1 - r) + r ^ 2 * (-1)) r at h
  rw [hd] at h
  exact h

/-- At λ=1, J(r)=r²(1-r) satisfies every binary inequality cited in the faulty
limit argument, while its derivative has φ(0)=0 and φ(1)=-1.  Consequently those
binary inequalities do not imply the claimed endpoint bound.  This does not
assert that this J comes from an activation with distortion at most 3. -/
theorem a2_direct_counterexample :
    (∀ p ∈ Set.Icc (0 : ℝ) 1,
      p * ((1 - p) ^ 2 * (1 - (1 - p))) ≤ p ^ 2 * (1 - p)) ∧
    (∀ r : ℝ, 2 * r - 3 * r ^ 2 ≤ 1 - r) ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < r ^ 2 * (1 - r)) ∧
    ((0 : ℝ) ^ 2 * (1 - 0) = 0) ∧
    ((1 : ℝ) ^ 2 * (1 - 1) = 0) ∧
    (2 * (1 : ℝ) - 3 * 1 ^ 2 = -1) ∧
    ¬ (-(2 * (1 : ℝ) - 3 * 1 ^ 2) / 1 ≤ 2 * 0 - 3 * 0 ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have h := mul_nonneg (pow_nonneg hp.1 3) (sub_nonneg.mpr hp.2)
    nlinarith
  · intro r
    nlinarith [sq_nonneg (r - 1 / 2)]
  · intro r hr
    exact mul_pos (sq_pos_of_pos hr.1) (sub_pos.mpr hr.2)
  all_goals norm_num

/-- Algebra for repairing A.3's auxiliary voter pair: the unsupported candidate
can be inserted at any rank with positive centered value `phiRank`.  The class
activation balances while the unsupported candidate becomes strictly stable.
Realizing these activations with rankings and rational voter weights is separate. -/
theorem auxiliary_pair_at_positive_rank (R P phiRank : ℝ)
    (hR : 0 < R) (hP : 0 < P) (hphi : 0 < phiRank) :
    R * P + P * (-R) = 0 ∧
      R * (-phiRank) + P * (-phiRank) < 0 := by
  constructor
  · ring
  · have h := mul_pos (add_pos hR hP) hphi
    nlinarith

/-- A positive primitive supplies a positive rank value somewhere; positivity
at the particular endpoint 0 is unnecessary for the auxiliary-pair argument. -/
theorem positive_rank_of_positive_integral
    (phi : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hphi : IntervalIntegrable phi MeasureTheory.volume a b)
    (hpos : 0 < ∫ r in a..b, phi r) :
    ∃ r ∈ Set.Icc a b, 0 < phi r := by
  by_contra! hnone
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
      MeasureTheory.volume a b := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hab hphi hz hnone
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- Nonnegative accumulated slack gives the reverse of the inequality printed
in B.1: before the matching endpoint, `J ≥ Q - S`. -/
theorem backward_comparison_of_slack
    (J Q slack : ℝ → ℝ) (a b S : ℝ)
    (hJa : J a = Q a - slack a) (hJb : J b = Q b - slack b)
    (hmatch : J b = Q b - S) (hslack : slack a ≤ slack b) :
    Q a - S ≤ J a := by
  linarith

/-- Integral form of the backwards comparison. The two increment hypotheses
are exactly what the fundamental theorem of calculus supplies for primitives. -/
theorem backward_comparison_of_integrals
    (J Q phi psi : ℝ → ℝ) (a b S : ℝ)
    (hab : a ≤ b)
    (hphi : IntervalIntegrable phi MeasureTheory.volume a b)
    (hpsi : IntervalIntegrable psi MeasureTheory.volume a b)
    (hle : ∀ r ∈ Set.Icc a b, phi r ≤ psi r)
    (hJ : J b - J a = ∫ r in a..b, phi r)
    (hQ : Q b - Q a = ∫ r in a..b, psi r)
    (hmatch : J b = Q b - S) :
    Q a - S ≤ J a := by
  have hint := intervalIntegral.integral_mono_on hab hphi hpsi hle
  linarith

/-- Even smooth polynomials refute the opposite local implication:
`J(r)=r²-r+1` and `Q(r)=r` agree at 1 and have `J'≤Q'` on [0,1],
but `J(0)>Q(0)`. The slope values are stated algebraically here. -/
theorem backward_comparison_counterexample :
    ((1 : ℝ) ^ 2 - 1 + 1 = 1) ∧
    (∀ r ∈ Set.Icc (0 : ℝ) 1, 2 * r - 1 ≤ 1) ∧
    ¬ ((0 : ℝ) ^ 2 - 0 + 1 ≤ 0) := by
  constructor
  · norm_num
  constructor
  · intro r hr
    linarith [hr.2]
  · norm_num

/-- The slope in the preceding counterexample is the actual derivative. -/
theorem backward_counterexample_derivative (r : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 - t + 1) (2 * r - 1) r := by
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  exact (hp.sub (hasDerivAt_id r)).add_const 1

/-- The cap and transition estimates suffice to preserve the endpoint,
without asserting the stronger (unnecessary) identity on all of [b,e]. -/
theorem endpoint_domination_of_three_regions
    (J Q : ℝ → ℝ) (l a b e S cap mu : ℝ)
    (hlow : ∀ r ∈ Set.Icc l a, J r ≤ cap)
    (hcap : cap < Q b - S)
    (htransition : ∀ r ∈ Set.Icc a b, J r ≤ Q b - S + mu)
    (hmiddle : ∀ r ∈ Set.Icc b e, J r ≤ Q e - S)
    (hmu : 0 ≤ mu) (hgap : Q b + mu < Q e)
    (hendpoint : J e = Q e - S) :
    ∀ r ∈ Set.Icc l e, J r ≤ J e := by
  intro r hr
  rw [hendpoint]
  by_cases hra : r ≤ a
  · have h := hlow r ⟨hr.1, hra⟩
    linarith
  by_cases hrb : r ≤ b
  · have h := htransition r ⟨le_of_lt (lt_of_not_ge hra), hrb⟩
    linarith
  · exact hmiddle r ⟨le_of_lt (lt_of_not_ge hrb), hr.2⟩

/-- If the original endpoint dominates its prefix and the floor, taking the
running maximum with that floor preserves the endpoint exactly. -/
theorem running_envelope_preserves_endpoint
    (J : ℝ → ℝ) (l e floor : ℝ) (hle : l ≤ e)
    (hfloor : floor ≤ J e)
    (hdom : ∀ r ∈ Set.Icc l e, J r ≤ J e) :
    max floor (sSup (J '' Set.Icc l e)) = J e := by
  have hmem : J e ∈ J '' Set.Icc l e := ⟨e, ⟨hle, le_rfl⟩, rfl⟩
  have hbdd : BddAbove (J '' Set.Icc l e) := by
    refine ⟨J e, ?_⟩
    rintro v ⟨r, hr, rfl⟩
    exact hdom r hr
  have hs : sSup (J '' Set.Icc l e) = J e := by
    apply le_antisymm
    · apply csSup_le ⟨J e, hmem⟩
      rintro v ⟨r, hr, rfl⟩
      exact hdom r hr
    · exact le_csSup hbdd hmem
  rw [hs, max_eq_right hfloor]

noncomputable def quadraticPrimitive (lam r : ℝ) : ℝ := lam * r - r ^ 2 / 2

/-- Exact arithmetic for the endpoint repair: the room from x+=.38 to
te=.385 exceeds the entire slack budget μ₀=.00025509854. -/
theorem endpoint_gap_exceeds_slack (lam : ℝ)
    (hlam : (562325 : ℝ) / 1000000 ≤ lam) :
    quadraticPrimitive lam ((38 : ℝ) / 100) +
      (25509854 : ℝ) / 100000000000 <
        quadraticPrimitive lam ((385 : ℝ) / 1000) := by
  unfold quadraticPrimitive
  nlinarith

/-- The lower bound .000899125 on that room is itself checked exactly. -/
theorem endpoint_gap_lower_bound (lam : ℝ)
    (hlam : (562325 : ℝ) / 1000000 ≤ lam) :
    (899125 : ℝ) / 1000000000 ≤
      quadraticPrimitive lam ((385 : ℝ) / 1000) -
        quadraticPrimitive lam ((38 : ℝ) / 100) := by
  unfold quadraticPrimitive
  nlinarith

end ManuscriptCorrections
end OptimalG
