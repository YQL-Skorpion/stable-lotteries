import OptimalG.FiniteVerifier
import OptimalG.HighMassTest
import OptimalG.SplitBounds
import OptimalG.MiddleRankConvexity

/-! Assembly of the all-mass verifier from the analytic subrange tests. -/
namespace OptimalG
open Set

/-- Independent coefficient choices for each mass assemble into a single verifier.
No regularity of these choices is required. -/
theorem verifier_of_pointwise {phi : ℝ → ℝ} {lam : ℝ}
    (hv : ∀ p ∈ Ioo (0 : ℝ) 1, ∃ beta : ℝ, ∃ corr : ℝ → ℝ,
      VerifierOn {p} phi lam (fun _ => beta) (fun _ x => corr x)) :
    ∃ beta corr, VerifierOn (Ioo 0 1) phi lam beta corr := by
  classical
  have hh : ∀ p : ℝ, ∃ beta : ℝ, ∃ corr : ℝ → ℝ,
      p ∈ Ioo (0 : ℝ) 1 → VerifierOn {p} phi lam (fun _ => beta) (fun _ x => corr x) := by
    intro p
    by_cases hp : p ∈ Ioo (0 : ℝ) 1
    · obtain ⟨b, c, hc⟩ := hv p hp
      exact ⟨b, c, fun _ => hc⟩
    · exact ⟨0, fun _ => 0, fun h => False.elim (hp h)⟩
  choose beta corr hbc using hh
  refine ⟨beta, corr, ?_⟩
  constructor
  · intro p hp; exact (hbc p hp).beta_nonneg p rfl
  · intro p hp; exact (hbc p hp).corr_nonneg p rfl
  · intro p hp; exact (hbc p hp).low_first p rfl
  · intro p hp; exact (hbc p hp).low_second p rfl
  · intro p hp; exact (hbc p hp).high_first p rfl
  · intro p hp; exact (hbc p hp).high_second p rfl

theorem verifier_pointwise_distortion {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
    (hv : ∀ p ∈ Ioo (0 : ℝ) 1, ∃ beta : ℝ, ∃ corr : ℝ → ℝ,
      VerifierOn {p} phi lam (fun _ => beta) (fun _ x => corr x)) :
    maximumDistortion (normalizedActivation phi) ≤ ENNReal.ofReal (1 + 2 * lam) := by
  obtain ⟨beta, corr, hbc⟩ := verifier_of_pointwise hv
  exact verifier_maximumDistortion h beta corr hbc

/-- The supporting-line and q=0 high-rank conditions generate the whole
three-function test on a variational mass interval. -/
theorem threeFunctionTest_of_supports {phi : ℝ → ℝ} {lam p beta eta z0 : ℝ}
    (h : VerifierCurve phi lam) (hp0 : 0 < p) (hpl : p ≤ lam)
    (hz0 : lam ≤ z0) (hz01 : z0 ≤ 1) (hb : 0 ≤ beta) (heta : 0 ≤ eta)
    (hetab : eta ≤ 1 + beta * p)
    (hlow : ∀ u ∈ Icc (0 : ℝ) lam, phi 0 - u ≤ phi u)
    (hline : ∀ z ∈ Icc lam z0, phi z = lam - z)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ z0 → a - b ≤ phi b - phi a)
    (hgap : 1 ≤ beta * (phi 0 - lam + z0 - p))
    (hsupport1 : ∀ x ∈ Icc (0 : ℝ) lam,
      x + eta * phi x ≤ 2 * lam - beta * curvePrimitive phi (1 - p))
    (hsupport2 : ∀ y ∈ Icc p lam,
      y + eta * phi y ≤ lam - p + beta * curvePrimitive phi p)
    (hbase : ∀ z ∈ Icc z0 1, z - lam + beta * packingK phi p 0 z + eta * phi z ≤ 0) :
    ThreeFunctionTest phi lam p beta eta := by
  have hsecond := secondTest_of_endpoint h hp0 hpl hb hetab (by
    intro y hy
    have hh := hsupport2 y hy
    linarith)
  have hgap1 : 1 ≤ beta * (phi 0 - lam + 1 - p) :=
    hgap.trans (mul_le_mul_of_nonneg_left (by linarith) hb)
  refine ⟨hb, heta, h.firstTest_of_support hlow ⟨hp0.le, hpl⟩ hb hgap1 hsupport1, hsecond, ?_⟩
  intro z hz q hq hqp
  by_cases hzz : z ≤ z0
  · apply h.thirdTest_middle_of_endpoints hq hqp hpl hz0 hz01 hb hline hfall _ _ z ⟨hz.1, hzz⟩
    · have hh := hsecond lam ⟨hpl, le_rfl⟩ q hq hqp
      linarith
    · exact h.thirdTest_of_zero_split hlow ⟨hp0.le, hpl⟩ hz0 hb hgap hbase
        z0 ⟨le_rfl, hz01⟩ q hq hqp
  · exact h.thirdTest_of_zero_split hlow ⟨hp0.le, hpl⟩ hz0 hb hgap hbase
      z ⟨le_of_not_ge hzz, hz.2⟩ q hq hqp

end OptimalG
