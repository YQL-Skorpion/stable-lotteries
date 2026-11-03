import OptimalG.Certificates.IntegerValidity
import OptimalG.Certificates.IntegerTranscendental

namespace OptimalG.Certificates.RatExpr
variable {n : ℕ}

def enclosureCheck (s : ℕ) (e : RatExpr n) (box : Fin n→IntegerInterval)
    (out : IntegerInterval) : Bool :=
  match e.integerInterval s box with
  | none => false
  | some result => result.subsetCheck out

theorem enclosureCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr n)
    (box : Fin n→IntegerInterval) (out : IntegerInterval)
    (hc : e.enclosureCheck s box out=true) (x : Fin n→ℝ)
    (hx : ∀ i,(box i).Contains s (x i)) : out.Contains s (e.eval x) := by
  cases he : e.integerInterval s box with
  | none => simp [enclosureCheck,he] at hc
  | some result =>
    exact IntegerInterval.subsetCheck_sound (integerInterval_sound hs box x hx e he)
      (by simpa only [enclosureCheck,he] using hc)

theorem enclosureCheck_valid {s : ℕ} (hs : 0<s) (e : RatExpr n)
    (box : Fin n→IntegerInterval) (out : IntegerInterval)
    (hc : e.enclosureCheck s box out=true) (x : Fin n→ℝ)
    (hx : ∀ i,(box i).Contains s (x i)) : e.Valid x := by
  cases he : e.integerInterval s box with
  | none => simp [enclosureCheck,he] at hc
  | some result => exact integerInterval_valid hs box x hx e he

def enclosureRefinedCheck (s k : ℕ) (e : RatExpr n) (box : Fin n→IntegerInterval)
    (out : IntegerInterval) : Bool :=
  e.enclosureCheck (k*s) (fun i => (box i).rescale k) (out.rescale k)

theorem enclosureRefinedCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k) (e : RatExpr n)
    (box : Fin n→IntegerInterval) (out : IntegerInterval)
    (hc : e.enclosureRefinedCheck s k box out=true) (x : Fin n→ℝ)
    (hx : ∀ i,(box i).Contains s (x i)) : out.Contains s (e.eval x) := by
  apply (IntegerInterval.rescale_contains_iff hk s out _).mp
  exact enclosureCheck_sound (Nat.mul_pos hk hs) e _ _ hc x
    (fun i => (IntegerInterval.rescale_contains_iff hk s (box i) _).mpr (hx i))

end OptimalG.Certificates.RatExpr
