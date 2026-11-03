import OptimalG.Certificates.Interval

/-!
# Reified rational expressions and certified box subdivision

An expression has an ordinary real interpretation and an exact rational
interval interpretation. The latter may reject divisions whose denominators
are not separated from zero. `checkLower_sound` proves that a finite tree of
successful checks covers the whole input box, including split boundaries.
-/

namespace OptimalG.Certificates

inductive RatExpr (n : ℕ) where
  | const : ℚ → RatExpr n
  | var : Fin n → RatExpr n
  | neg : RatExpr n → RatExpr n
  | add : RatExpr n → RatExpr n → RatExpr n
  | mul : RatExpr n → RatExpr n → RatExpr n
  | inv : RatExpr n → RatExpr n
  deriving DecidableEq, Repr

namespace RatExpr

variable {n : ℕ}

instance : Neg (RatExpr n) := ⟨RatExpr.neg⟩
instance : Add (RatExpr n) := ⟨RatExpr.add⟩
instance : Mul (RatExpr n) := ⟨RatExpr.mul⟩
instance : Sub (RatExpr n) := ⟨fun a b => a.add b.neg⟩
instance : Div (RatExpr n) := ⟨fun a b => a.mul b.inv⟩
instance (k : ℕ) : OfNat (RatExpr n) k := ⟨.const k⟩

noncomputable def eval (x : Fin n → ℝ) : RatExpr n → ℝ
  | .const q => q
  | .var i => x i
  | .neg a => -(a.eval x)
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x
  | .inv a => (a.eval x)⁻¹

def interval (box : Fin n → RatInterval) : RatExpr n → Option RatInterval
  | .const q => some (.point q)
  | .var i => some (box i)
  | .neg a => do return (← a.interval box).neg
  | .add a b => do return (← a.interval box).add (← b.interval box)
  | .mul a b => do return (← a.interval box).mul (← b.interval box)
  | .inv a => do (← a.interval box).reciprocal

theorem interval_sound (box : Fin n → RatInterval) (x : Fin n → ℝ)
    (hx : ∀ i, (box i).Contains (x i)) (e : RatExpr n)
    {a : RatInterval} (ha : e.interval box = some a) : a.Contains (e.eval x) := by
  induction e generalizing a with
  | const q =>
    have h := Option.some.inj ha
    subst a
    exact RatInterval.point_contains q
  | var i =>
    have h := Option.some.inj ha
    subst a
    exact hx i
  | neg e ih =>
    cases he : e.interval box with
    | none => simp [interval, he] at ha
    | some b =>
      simp [interval, he] at ha
      subst a
      exact RatInterval.neg_contains (ih he)
  | add e f ihe ihf =>
    cases he : e.interval box with
    | none => simp [interval, he] at ha
    | some b =>
      cases hf : f.interval box with
      | none => simp [interval, he, hf] at ha
      | some c =>
        simp [interval, he, hf] at ha
        subst a
        exact RatInterval.add_contains (ihe he) (ihf hf)
  | mul e f ihe ihf =>
    cases he : e.interval box with
    | none => simp [interval, he] at ha
    | some b =>
      cases hf : f.interval box with
      | none => simp [interval, he, hf] at ha
      | some c =>
        simp [interval, he, hf] at ha
        subst a
        exact RatInterval.mul_contains (ihe he) (ihf hf)
  | inv e ih =>
    cases he : e.interval box with
    | none => simp [interval, he] at ha
    | some b =>
      simp [interval, he] at ha
      exact RatInterval.reciprocal_contains (ih he) ha

/-- Exact lower-bound check on a single rectangular box. -/
def lowerCheck (e : RatExpr n) (box : Fin n → RatInterval) (bound : ℚ) : Bool :=
  match e.interval box with
  | none => false
  | some a => decide (bound < a.lo)

theorem lowerCheck_sound (e : RatExpr n) (box : Fin n → RatInterval) (bound : ℚ)
    (hcheck : e.lowerCheck box bound = true) (x : Fin n → ℝ)
    (hx : ∀ i, (box i).Contains (x i)) : (bound : ℝ) < e.eval x := by
  cases he : e.interval box with
  | none => simp [lowerCheck, he] at hcheck
  | some a =>
    have hlo : bound < a.lo := by simpa [lowerCheck, he] using hcheck
    have hreal : (bound : ℝ) < a.lo := by exact_mod_cast hlo
    exact hreal.trans_le (interval_sound box x hx e he).1

end RatExpr

/-- A finite proof of box coverage; a split is on one coordinate at an exact
rational location. No sampled values are used. -/
inductive BoxCertificate (n : ℕ) where
  | leaf : BoxCertificate n
  | split : Fin n → ℚ → BoxCertificate n → BoxCertificate n → BoxCertificate n
  deriving DecidableEq, Repr

namespace BoxCertificate

variable {n : ℕ}

def leftBox (box : Fin n → RatInterval) (i : Fin n) (m : ℚ) : Fin n → RatInterval :=
  Function.update box i ⟨(box i).lo, m⟩

def rightBox (box : Fin n → RatInterval) (i : Fin n) (m : ℚ) : Fin n → RatInterval :=
  Function.update box i ⟨m, (box i).hi⟩

def checkLower (e : RatExpr n) (box : Fin n → RatInterval) (bound : ℚ) :
    BoxCertificate n → Bool
  | .leaf => e.lowerCheck box bound
  | .split i m left right =>
      checkLower e (leftBox box i m) bound left &&
      checkLower e (rightBox box i m) bound right

/-- A certificate is accepted only when every leaf proves its bound, and the
split theorem ensures those leaves cover every real point in the initial box. -/
theorem checkLower_sound (e : RatExpr n) (bound : ℚ) (t : BoxCertificate n) :
    ∀ (box : Fin n → RatInterval), t.checkLower e box bound = true →
    ∀ (x : Fin n → ℝ), (∀ i, (box i).Contains (x i)) → (bound : ℝ) < e.eval x := by
  induction t with
  | leaf =>
    intro box ht x hx
    exact RatExpr.lowerCheck_sound e box bound ht x hx
  | split i m left right ihl ihr =>
    intro box ht x hx
    have hchecks : checkLower e (leftBox box i m) bound left = true ∧
        checkLower e (rightBox box i m) bound right = true := by
      simpa [checkLower] using ht
    by_cases hm : x i ≤ (m : ℝ)
    · apply ihl (leftBox box i m) hchecks.1 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [leftBox, RatInterval.Contains] using And.intro (hx i).1 hm
      · simpa [leftBox, Function.update_of_ne hji] using hx j
    · apply ihr (rightBox box i m) hchecks.2 x
      intro j
      by_cases hji : j = i
      · subst j
        simpa [rightBox, RatInterval.Contains] using And.intro (le_of_not_ge hm) (hx i).2
      · simpa [rightBox, Function.update_of_ne hji] using hx j

end BoxCertificate
end OptimalG.Certificates
