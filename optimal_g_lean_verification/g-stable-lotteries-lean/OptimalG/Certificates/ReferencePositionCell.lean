import OptimalG.Certificates.ReferenceScalarExpressions
import OptimalG.Certificates.IntegerEnclosures
import OptimalG.Certificates.ExpressionCleanup

/-! Positional first variations are enclosed after exact cancellation. The
actual reference deficit enters through its proved error from the cubic. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr

namespace ReferenceScalarCell

def alphaCoordinateExpr (c : ReferenceScalarCell) (j : Fin 16) : RatExpr 1 :=
  (partialExpr j c.alphaSource).substitute c.frozenSubstitution

def betaCoordinateExpr (c : ReferenceScalarCell) (j : Fin 16) : RatExpr 1 :=
  (partialExpr j c.betaSource).substitute c.frozenSubstitution

def positionalNominalExpr (c : ReferenceScalarCell) (j : Fin 16) : RatExpr 1 :=
  c.alphaCoordinateExpr j*c.flow.valueExpr+c.betaCoordinateExpr j

theorem alphaCoordinateExpr_eval (c : ReferenceScalarCell) (j : Fin 16) (t : ℝ) :
    (c.alphaCoordinateExpr j).evalOne t=(partialExpr j c.alphaSource).eval (c.frozenInput t) :=
  RatExpr.substitute_eval _ _ _

theorem betaCoordinateExpr_eval (c : ReferenceScalarCell) (j : Fin 16) (t : ℝ) :
    (c.betaCoordinateExpr j).evalOne t=(partialExpr j c.betaSource).eval (c.frozenInput t) :=
  RatExpr.substitute_eval _ _ _

theorem positionalNominalExpr_eval (c : ReferenceScalarCell) (j : Fin 16) (t : ℝ) :
    (c.positionalNominalExpr j).evalOne t=
      (partialExpr j c.alphaSource).eval (c.frozenInput t)*c.flow.valuePolynomial.eval t+
        (partialExpr j c.betaSource).eval (c.frozenInput t) := by
  simp only [positionalNominalExpr,evalOne,eval_addNotation,eval_mulNotation,
    ReferenceFlowCell.valueExpr,polynomial_eval,eval]
  rw [show (c.alphaCoordinateExpr j).eval (fun _ => t)=
      (partialExpr j c.alphaSource).eval (c.frozenInput t) from c.alphaCoordinateExpr_eval j t,
    show (c.betaCoordinateExpr j).eval (fun _ => t)=
      (partialExpr j c.betaSource).eval (c.frozenInput t) from c.betaCoordinateExpr_eval j t]

end ReferenceScalarCell

structure ReferencePositionCell where
  cell : ReferenceScalarCell
  coordinate : Fin 16
  exponential : IntegerInterval
  terminal : IntegerInterval
  flowError : IntegerInterval
  alphaDerivative : IntegerInterval
  nominal : IntegerInterval
  force : IntegerInterval

namespace ReferencePositionCell

def combinedExpr : RatExpr 5 := .var 0*(.var 1+.var 2*.var 3)/.var 4

def combinedBox (c : ReferencePositionCell) : Fin 5→IntegerInterval :=
  ![c.exponential,c.nominal,c.alphaDerivative,c.flowError,c.terminal]

def check (s k : ℕ) (c : ReferencePositionCell) : Bool :=
  (c.cell.alphaCoordinateExpr c.coordinate).cleanup.enclosureRefinedCheck
      s k (fun _ => ⟨0,s⟩) c.alphaDerivative &&
  (c.cell.positionalNominalExpr c.coordinate).cleanup.enclosureRefinedCheck
      s k (fun _ => ⟨0,s⟩) c.nominal &&
  combinedExpr.enclosureRefinedCheck s k c.combinedBox c.force

theorem checked_force {s k : ℕ} (hs : 0<s) (hk : 0<k) (c : ReferencePositionCell)
    (hc : c.check s k=true) {t E Z terminal : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hE : c.exponential.Contains s E) (hterminal : c.terminal.Contains s terminal)
    (herror : c.flowError.Contains s (Z-c.cell.flow.valuePolynomial.eval t)) :
    c.force.Contains s (E*((partialExpr c.coordinate c.cell.alphaSource).eval (c.cell.frozenInput t)*Z+
      (partialExpr c.coordinate c.cell.betaSource).eval (c.cell.frozenInput t))/terminal) := by
  obtain ⟨hab,hforce⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hab
  have hunit : ∀ j : Fin 1,(⟨0,(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro j
    constructor <;> dsimp [IntegerInterval.Contains]
    · simpa using (mul_nonneg (show (0:ℝ)≤s by positivity) ht.1)
    · simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)
  have hda := RatExpr.enclosureRefinedCheck_sound hs hk
    (c.cell.alphaCoordinateExpr c.coordinate).cleanup (fun _ => ⟨0,s⟩)
    c.alphaDerivative ha (fun _ => t) hunit
  have hnom := RatExpr.enclosureRefinedCheck_sound hs hk
    (c.cell.positionalNominalExpr c.coordinate).cleanup (fun _ => ⟨0,s⟩)
    c.nominal hb (fun _ => t) hunit
  rw [RatExpr.cleanup_eval] at hda hnom
  have hx : ∀ j,(c.combinedBox j).Contains s
      (![E,(c.cell.positionalNominalExpr c.coordinate).evalOne t,
        (c.cell.alphaCoordinateExpr c.coordinate).evalOne t,
        Z-c.cell.flow.valuePolynomial.eval t,terminal] j) := by
    intro j
    fin_cases j
    · simpa [combinedBox] using hE
    · simpa [combinedBox,evalOne] using hnom
    · simpa [combinedBox,evalOne] using hda
    · simpa [combinedBox] using herror
    · simpa [combinedBox] using hterminal
  have hf := RatExpr.enclosureRefinedCheck_sound hs hk combinedExpr c.combinedBox c.force
    hforce _ hx
  have he : combinedExpr.eval
      ![E,(c.cell.positionalNominalExpr c.coordinate).evalOne t,
        (c.cell.alphaCoordinateExpr c.coordinate).evalOne t,
        Z-c.cell.flow.valuePolynomial.eval t,terminal]=
      E*((partialExpr c.coordinate c.cell.alphaSource).eval (c.cell.frozenInput t)*Z+
        (partialExpr c.coordinate c.cell.betaSource).eval (c.cell.frozenInput t))/terminal := by
    simp [combinedExpr,eval_divNotation,eval_mulNotation,eval_addNotation,eval,
      ReferenceScalarCell.positionalNominalExpr_eval,ReferenceScalarCell.alphaCoordinateExpr_eval]
    ring
  rwa [he] at hf

end ReferencePositionCell
end OptimalG.Certificates.Transport
