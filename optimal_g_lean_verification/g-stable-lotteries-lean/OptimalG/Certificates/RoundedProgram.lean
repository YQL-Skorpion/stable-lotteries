import OptimalG.Certificates.Transcendental

/-!
# Checked rounded arithmetic programs

Every instruction carries proposed rational output endpoints. Acceptance checks
that those endpoints enclose the exact rational arithmetic result. Thus an
untrusted generator can use fixed-size dyadics without accumulating enormous
denominators, while the real-number semantics remains kernel-verified.

Registers are indexed from the most recently produced value. Reading past the
register list returns zero in both the real and interval semantics.
-/

namespace OptimalG.Certificates

namespace RatInterval

def subsetCheck (a b : RatInterval) : Bool := decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi)

theorem subsetCheck_contains {a b : RatInterval} {x : ℝ}
    (hx : a.Contains x) (hab : a.subsetCheck b = true) : b.Contains x := by
  have h : b.lo ≤ a.lo ∧ a.hi ≤ b.hi := by simpa [subsetCheck] using hab
  constructor
  · exact (show (b.lo:ℝ) ≤ a.lo by exact_mod_cast h.1).trans hx.1
  · exact hx.2.trans (show (a.hi:ℝ) ≤ b.hi by exact_mod_cast h.2)

def minimum (a b : RatInterval) : RatInterval := ⟨min a.lo b.lo, min a.hi b.hi⟩
def maximum (a b : RatInterval) : RatInterval := ⟨max a.lo b.lo, max a.hi b.hi⟩

theorem minimum_contains {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.minimum b).Contains (min x y) := by
  simpa [minimum, Contains] using And.intro (min_le_min hx.1 hy.1) (min_le_min hx.2 hy.2)

theorem maximum_contains {a b : RatInterval} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.maximum b).Contains (max x y) := by
  simpa [maximum, Contains] using And.intro (max_le_max hx.1 hy.1) (max_le_max hx.2 hy.2)

end RatInterval

namespace RoundedProgram

inductive Instruction where
  | const (q : ℚ)
  | neg (i : ℕ)
  | add (i j : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  | min (i j : ℕ)
  | max (i j : ℕ)
  | exp (i order : ℕ)
  | sqrt (i : ℕ)
  deriving DecidableEq, Repr

def readBound (env : List RatInterval) (i : ℕ) : RatInterval := env.getD i (.point 0)
noncomputable def readReal (env : List ℝ) (i : ℕ) : ℝ := env.getD i 0

def Encloses (bounds : List RatInterval) (values : List ℝ) : Prop :=
  ∀ i, (readBound bounds i).Contains (readReal values i)

theorem encloses_nil : Encloses [] [] := by
  intro i
  simpa [readBound, readReal] using RatInterval.point_contains 0

theorem encloses_cons {bs : List RatInterval} {vs : List ℝ} {b : RatInterval} {v : ℝ}
    (h : Encloses bs vs) (hv : b.Contains v) : Encloses (b::bs) (v::vs) := by
  intro i
  cases i with
  | zero => simpa [readBound, readReal] using hv
  | succ i => simpa [readBound, readReal] using h i

noncomputable def Instruction.eval (env : List ℝ) : Instruction → ℝ
  | .const q => q
  | .neg i => -readReal env i
  | .add i j => readReal env i + readReal env j
  | .mul i j => readReal env i * readReal env j
  | .inv i => (readReal env i)⁻¹
  | .min i j => Min.min (readReal env i) (readReal env j)
  | .max i j => Max.max (readReal env i) (readReal env j)
  | .exp i _ => Real.exp (readReal env i)
  | .sqrt i => Real.sqrt (readReal env i)

def Instruction.check (env : List RatInterval) (out : RatInterval) : Instruction → Bool
  | .const q => (RatInterval.point q).subsetCheck out
  | .neg i => (readBound env i).neg.subsetCheck out
  | .add i j => ((readBound env i).add (readBound env j)).subsetCheck out
  | .mul i j => ((readBound env i).mul (readBound env j)).subsetCheck out
  | .inv i => match (readBound env i).reciprocal with
      | none => false
      | some b => b.subsetCheck out
  | .min i j => ((readBound env i).minimum (readBound env j)).subsetCheck out
  | .max i j => ((readBound env i).maximum (readBound env j)).subsetCheck out
  | .exp i n => match (readBound env i).expEnclosure n with
      | none => false
      | some b => b.subsetCheck out
  | .sqrt i => (readBound env i).sqrtCheck out

theorem Instruction.check_sound {bs : List RatInterval} {vs : List ℝ}
    (h : Encloses bs vs) (op : Instruction) (out : RatInterval)
    (hc : op.check bs out = true) : out.Contains (op.eval vs) := by
  cases op with
  | const q => exact RatInterval.subsetCheck_contains (RatInterval.point_contains q) hc
  | neg i => exact RatInterval.subsetCheck_contains (RatInterval.neg_contains (h i)) hc
  | add i j => exact RatInterval.subsetCheck_contains (RatInterval.add_contains (h i) (h j)) hc
  | mul i j => exact RatInterval.subsetCheck_contains (RatInterval.mul_contains (h i) (h j)) hc
  | inv i =>
    simp only [Instruction.check] at hc
    split at hc
    next he => simp at hc
    next b he => exact RatInterval.subsetCheck_contains (RatInterval.reciprocal_contains (h i) he) hc
  | min i j => exact RatInterval.subsetCheck_contains (RatInterval.minimum_contains (h i) (h j)) hc
  | max i j => exact RatInterval.subsetCheck_contains (RatInterval.maximum_contains (h i) (h j)) hc
  | exp i n =>
    simp only [Instruction.check] at hc
    split at hc
    next he => simp at hc
    next b he => exact RatInterval.subsetCheck_contains (RatInterval.expEnclosure_contains (h i) he) hc
  | sqrt i => exact RatInterval.sqrtCheck_contains (h i) hc

structure Step where
  instruction : Instruction
  enclosure : RatInterval
  deriving DecidableEq, Repr

def check (env : List RatInterval) : List Step → Bool
  | [] => true
  | s::ss => s.instruction.check env s.enclosure && check (s.enclosure::env) ss

def bounds (env : List RatInterval) : List Step → List RatInterval
  | [] => env
  | s::ss => bounds (s.enclosure::env) ss

noncomputable def eval (env : List ℝ) : List Step → List ℝ
  | [] => env
  | s::ss => eval (s.instruction.eval env::env) ss

theorem check_sound (program : List Step) {bs : List RatInterval} {vs : List ℝ}
    (h : Encloses bs vs) (hc : check bs program = true) :
    Encloses (bounds bs program) (eval vs program) := by
  induction program generalizing bs vs with
  | nil => exact h
  | cons s ss ih =>
    have hh : s.instruction.check bs s.enclosure = true ∧ check (s.enclosure::bs) ss = true := by
      simpa only [check, Bool.and_eq_true] using hc
    exact ih (encloses_cons h (s.instruction.check_sound h s.enclosure hh.1)) hh.2

/-- A certificate can be split into independently checked chunks. -/
theorem check_append (as bs : List Step) (env : List RatInterval) :
    check env (as++bs) = (check env as && check (bounds env as) bs) := by
  induction as generalizing env with
  | nil => simp [check, bounds]
  | cons s ss ih => simp [check, bounds, ih, Bool.and_assoc]

theorem eval_append (as bs : List Step) (env : List ℝ) :
    eval env (as++bs) = eval (eval env as) bs := by
  induction as generalizing env with
  | nil => rfl
  | cons s ss ih => exact ih _

end RoundedProgram
end OptimalG.Certificates
