import OptimalG.Certificates.ReferenceBaseCoefficients
import OptimalG.Certificates.IntegerEnclosures
import OptimalG.Certificates.ExpressionCleanup

/-! Finite reference-weight arithmetic. The analytic inputs are explicitly the
actual adjoint exponent, actual deficit and terminal deficit. The coefficient
is evaluated from the same transported expressions used in the Taylor proof. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr

structure ReferenceWeightCell where
  flow : ReferenceFlowCell
  exponent : IntegerInterval
  exponential : IntegerInterval
  deficit : IntegerInterval
  terminal : IntegerInterval
  bases : Fin 4→IntegerInterval
  weights : Fin 4→IntegerInterval

namespace ReferenceWeightCell

def weightExpr (i : Fin 4) : RatExpr 4 :=
  if i<2 then .var 0*.var 1*.var 2/.var 3 else .var 0*.var 1/.var 3

def weightBox (c : ReferenceWeightCell) (i : Fin 4) : Fin 4→IntegerInterval :=
  ![c.exponential,c.bases i,c.deficit,c.terminal]

def check (s k : ℕ) (c : ReferenceWeightCell) : Bool :=
  (List.finRange 4).all (fun i => (c.flow.baseCoefficientExpr i).cleanup.enclosureRefinedCheck
      s k (fun _ => ⟨0,s⟩) (c.bases i)) &&
    (c.exponent.expRefinedCheck s k 16 c.exponential &&
      (List.finRange 4).all (fun i => (weightExpr i).enclosureRefinedCheck
        s k (c.weightBox i) (c.weights i)))

theorem weightExpr_eval (i : Fin 4) (E A Z terminal : ℝ) :
    (weightExpr i).eval ![E,A,Z,terminal]=E*A*(if i<2 then Z else 1)/terminal := by
  fin_cases i <;> simp [weightExpr,eval_mulNotation,eval_divNotation,eval]

theorem checked_weights {s k : ℕ} (hs : 0<s) (hk : 0<k) (c : ReferenceWeightCell)
    (hc : c.check s k=true) {t exponent Z terminal : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (he : c.exponent.Contains s exponent)
    (hZ : c.deficit.Contains s Z) (hterm : c.terminal.Contains s terminal) (i : Fin 4) :
    (c.weights i).Contains s
      (Real.exp exponent*(c.flow.baseCoefficientExpr i).evalOne t*
        (if i<2 then Z else 1)/terminal) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hbcheck := List.all_eq_true.mp hh.1 i (List.mem_finRange i)
  have hexpcheck := (Bool.and_eq_true_iff.mp hh.2).1
  have hwcheck := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hh.2).2 i (List.mem_finRange i)
  have hunit : ∀ j : Fin 1,(⟨0,(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro j
    constructor <;> dsimp [IntegerInterval.Contains]
    · simpa using (mul_nonneg (show (0:ℝ)≤s by positivity) ht.1)
    · simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)
  have hb := RatExpr.enclosureRefinedCheck_sound hs hk (c.flow.baseCoefficientExpr i).cleanup
    (fun _ => ⟨0,s⟩) (c.bases i) hbcheck (fun _ => t) hunit
  rw [RatExpr.cleanup_eval] at hb
  have hE := IntegerInterval.expRefinedCheck_sound hs hk hexpcheck he
  have hx : ∀ j,(c.weightBox i j).Contains s
      (![Real.exp exponent,(c.flow.baseCoefficientExpr i).evalOne t,Z,terminal] j) := by
    intro j
    fin_cases j
    · simpa [weightBox] using hE
    · simpa [weightBox,RatExpr.evalOne] using hb
    · simpa [weightBox] using hZ
    · simpa [weightBox] using hterm
  have hw := RatExpr.enclosureRefinedCheck_sound hs hk (weightExpr i) (c.weightBox i)
    (c.weights i) hwcheck ![Real.exp exponent,(c.flow.baseCoefficientExpr i).evalOne t,Z,terminal] hx
  simpa only [weightExpr_eval] using hw

end ReferenceWeightCell
end OptimalG.Certificates.Transport
