import OptimalG.Certificates.IntegerExpression
import OptimalG.Certificates.DifferentiableExpression

/-! An accepted integer interval evaluation also proves that every actual
reciprocal denominator is nonzero, as needed for the calculus interpretation. -/
namespace OptimalG.Certificates
namespace IntegerInterval

theorem invRounded_nonzero {s : ℕ} {a b : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hc : a.invRounded s=some b) : x ≠ 0 := by
  intro hz
  subst x
  have hloR : (a.lo:ℝ) ≤ 0 := by simpa only [mul_zero] using hx.1
  have hhiR : (0:ℝ) ≤ a.hi := by simpa only [mul_zero] using hx.2
  have hlo : a.lo ≤ 0 := by exact_mod_cast hloR
  have hhi : 0 ≤ a.hi := by exact_mod_cast hhiR
  unfold invRounded at hc
  split_ifs at hc with hp hn
  · exact (not_lt_of_ge hlo) hp.1
  · exact (not_lt_of_ge hhi) hn.2

end IntegerInterval
namespace RatExpr
variable {n : ℕ}

theorem integerInterval_valid {s : ℕ} (hs : 0<s) (box : Fin n→IntegerInterval)
    (x : Fin n→ℝ) (hx : ∀ i,(box i).Contains s (x i)) (e : RatExpr n)
    {out : IntegerInterval} (hc : e.integerInterval s box=some out) : e.Valid x := by
  induction e generalizing out with
  | const q => trivial
  | var i => trivial
  | neg e ih =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a => exact ih he
  | add e f ihe ihf =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      cases hf : f.integerInterval s box with
      | none => simp [integerInterval,he,hf] at hc
      | some b => exact ⟨ihe he,ihf hf⟩
  | mul e f ihe ihf =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      cases hf : f.integerInterval s box with
      | none => simp [integerInterval,he,hf] at hc
      | some b => exact ⟨ihe he,ihf hf⟩
  | inv e ih =>
    cases he : e.integerInterval s box with
    | none => simp [integerInterval,he] at hc
    | some a =>
      simp [integerInterval,he] at hc
      exact ⟨ih he,IntegerInterval.invRounded_nonzero
        (integerInterval_sound hs box x hx e he) hc⟩

end RatExpr
end OptimalG.Certificates
