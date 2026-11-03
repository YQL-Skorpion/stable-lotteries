import OptimalG.Certificates.IntegerRounded
import OptimalG.Certificates.Expression

/-! Rational-expression evaluation by deterministic fixed-denominator integer
intervals. Every accepted lower bound concerns the actual real expression. -/
namespace OptimalG.Certificates.RatExpr
variable {n : ℕ}

def integerInterval (s : ℕ) (box : Fin n→IntegerInterval) : RatExpr n→Option IntegerInterval
  | .const q => some (IntegerInterval.pointRounded s q)
  | .var i => some (box i)
  | .neg e => do return (←e.integerInterval s box).negRounded
  | .add e f => do return (←e.integerInterval s box).addRounded (←f.integerInterval s box)
  | .mul e f => do return IntegerInterval.mulRounded s (←e.integerInterval s box) (←f.integerInterval s box)
  | .inv e => do (←e.integerInterval s box).invRounded s

theorem integerInterval_sound {s : ℕ} (hs : 0<s) (box : Fin n→IntegerInterval)
    (x : Fin n→ℝ) (hx : ∀ i,(box i).Contains s (x i)) (e : RatExpr n)
    {out : IntegerInterval} (hc : e.integerInterval s box=some out) :
    out.Contains s (e.eval x) := by
  induction e generalizing out with
  | const q =>
    have h := Option.some.inj hc
    subst out
    exact IntegerInterval.pointRounded_contains s q
  | var i =>
    have h := Option.some.inj hc
    subst out
    exact hx i
  | neg e ih =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      simp [integerInterval,he] at hc
      subst out
      exact IntegerInterval.negRounded_contains (ih he)
  | add e f ihe ihf =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      cases hf : f.integerInterval s box with
      | none => simp [integerInterval,he,hf] at hc
      | some b =>
        simp [integerInterval,he,hf] at hc
        subst out
        exact IntegerInterval.addRounded_contains (ihe he) (ihf hf)
  | mul e f ihe ihf =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      cases hf : f.integerInterval s box with
      | none => simp [integerInterval,he,hf] at hc
      | some b =>
        simp [integerInterval,he,hf] at hc
        subst out
        exact IntegerInterval.mulRounded_contains hs (ihe he) (ihf hf)
  | inv e ih =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      simp [integerInterval,he] at hc
      exact IntegerInterval.invRounded_contains hs (ih he) hc

/-- The target is an integer numerator at the same fixed denominator. -/
def integerLowerCheck (s : ℕ) (e : RatExpr n) (box : Fin n→IntegerInterval) (bound : ℤ) : Bool :=
  match e.integerInterval s box with
  | none => false
  | some out => decide (bound<out.lo)

theorem integerLowerCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr n)
    (box : Fin n→IntegerInterval) (bound : ℤ) (hc : integerLowerCheck s e box bound=true)
    (x : Fin n→ℝ) (hx : ∀ i,(box i).Contains s (x i)) :
    (bound:ℝ)/(s:ℝ)<e.eval x := by
  cases he : e.integerInterval s box with
  | none => simp [integerLowerCheck,he] at hc
  | some a =>
    have hb : bound<a.lo := by simpa [integerLowerCheck,he] using hc
    have hb' : (bound:ℝ)<a.lo := by exact_mod_cast hb
    have hs' : (0:ℝ)<s := by exact_mod_cast hs
    exact (div_lt_div_of_pos_right hb' hs').trans_le
      (IntegerInterval.lower_bound hs (integerInterval_sound hs box x hx e he))

end OptimalG.Certificates.RatExpr
