import OptimalG.Certificates.IntegralIntervalBounds
import OptimalG.Certificates.IntegerEnclosures

/-! Scalar rank-flux checks apply to the actual cumulative potential and
actual pushed-forward weight. No stationarity or density formula is assumed
by the arithmetic checker. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory RatExpr

structure ReferenceFluxCell where
  interval : IntegralCell
  flux : ℚ
  position : IntegerInterval
  weight : IntegerInterval
  partialPotential : IntegerInterval
  potential : IntegerInterval
  error : IntegerInterval
  errorMass : IntegerInterval

namespace ReferenceFluxCell

def errorExpr (flux : ℚ) : RatExpr 2 :=
  ((.var 0-.var 1-.const flux)*(.var 0-.var 1-.const flux))/(.var 0-.const flux-3)

def check (s k : ℕ) (c : ReferenceFluxCell) : Bool :=
  IntegerInterval.integralCheck s c.interval.lo c.interval.hi c.position c.interval.mass &&
  IntegerInterval.partialIntegralCheck s c.interval.lo c.interval.hi c.position c.partialPotential &&
  (c.partialPotential.addRounded c.interval.future).subsetCheck c.potential &&
  decide (3*(s:ℤ)≤c.weight.lo ∧ (c.flux+3)*(s:ℚ)<(c.potential.lo:ℚ)) &&
  (errorExpr c.flux).enclosureRefinedCheck s k ![c.potential,c.weight] c.error &&
  IntegerInterval.integralCheck s c.interval.lo c.interval.hi c.error c.errorMass

theorem checked_potential_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceFluxCell) (hc : c.check s k=true)
    {f : ℝ→ℝ} {r finish W : ℝ} (hr : r∈Icc (c.interval.lo:ℝ) c.interval.hi)
    (hf : IntervalIntegrable f volume (c.interval.lo:ℝ) c.interval.hi)
    (hfuture : IntervalIntegrable f volume (c.interval.hi:ℝ) finish)
    (hposition : ∀ᵐ x ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.position.Contains s (f x))
    (hF : c.interval.future.Contains s (∫ x in (c.interval.hi:ℝ)..finish,f x))
    (hW : c.weight.Contains s W) :
    let P := ∫ x in r..finish,f x
    c.potential.Contains s P ∧ 3≤W ∧ 0<P-c.flux-3 ∧
      c.error.Contains s ((P-W-c.flux)^2/(P-c.flux-3)) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  rcases hh with ⟨⟨⟨⟨⟨hmass,hpart⟩,hadd⟩,hpos⟩,herror⟩,herrMass⟩
  have hpot := IntegerInterval.cumulative_contains hs hpart hadd hr hf hfuture hposition hF
  have hpos' : 3*(s:ℤ)≤c.weight.lo ∧ (c.flux+3)*(s:ℚ)<(c.potential.lo:ℚ) := of_decide_eq_true hpos
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hwlo : (3:ℝ)≤(c.weight.lo:ℝ)/(s:ℝ) := by
    apply (le_div_iff₀ hs').mpr
    exact_mod_cast hpos'.1
  have hplow : (c.flux:ℝ)+3<(c.potential.lo:ℝ)/(s:ℝ) := by
    apply (lt_div_iff₀ hs').mpr
    exact_mod_cast hpos'.2
  have hden : 0<(∫ x in r..finish,f x)-(c.flux:ℝ)-3 := by
    linarith [IntegerInterval.lower_bound hs hpot]
  have hx : ∀ i,(![c.potential,c.weight] i).Contains s
      (![∫ x in r..finish,f x,W] i) := by
    intro i
    fin_cases i
    · simpa using hpot
    · simpa using hW
  have he := RatExpr.enclosureRefinedCheck_sound hs hk (errorExpr c.flux)
    ![c.potential,c.weight] c.error herror _ hx
  refine ⟨hpot,hwlo.trans (IntegerInterval.lower_bound hs hW),hden,?_⟩
  simpa [errorExpr,eval_divNotation,eval_mulNotation,eval_subNotation,eval,pow_two] using he

theorem checked_position_mass {s k : ℕ} (hs : 0<s) (c : ReferenceFluxCell)
    (hc : c.check s k=true) (horder : c.interval.lo≤c.interval.hi) {f : ℝ→ℝ}
    (hf : IntervalIntegrable f volume (c.interval.lo:ℝ) c.interval.hi)
    (hposition : ∀ᵐ x ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.position.Contains s (f x)) :
    c.interval.mass.Contains s (∫ x in (c.interval.lo:ℝ)..c.interval.hi,f x) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  exact IntegerInterval.integralCheck_sound hs hh.1.1.1.1.1 horder hf hposition

theorem checked_error_mass {s k : ℕ} (hs : 0<s) (c : ReferenceFluxCell)
    (hc : c.check s k=true) (horder : c.interval.lo≤c.interval.hi) {e : ℝ→ℝ}
    (he : IntervalIntegrable e volume (c.interval.lo:ℝ) c.interval.hi)
    (herror : ∀ᵐ x ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.error.Contains s (e x)) :
    c.errorMass.Contains s (∫ x in (c.interval.lo:ℝ)..c.interval.hi,e x) := by
  exact IntegerInterval.integralCheck_sound hs (Bool.and_eq_true_iff.mp hc).2 horder he herror

end ReferenceFluxCell
end OptimalG.Certificates.Transport
