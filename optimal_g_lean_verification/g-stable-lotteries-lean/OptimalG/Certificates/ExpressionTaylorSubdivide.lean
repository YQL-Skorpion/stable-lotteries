import OptimalG.Certificates.ExpressionTaylorClean
import OptimalG.Certificates.ExpressionSubstitution

/-! Binary subdivision proves a uniform residual bound on the whole unit
interval. A failed whole-cell enclosure may be split without changing the
polynomial trajectory or treating samples as a certificate. -/
namespace OptimalG.Certificates.RatExpr
open Set

def leftHalf (e : RatExpr 1) : RatExpr 1 := e.substitute (fun _ => .const (1/2)*.var 0)
def rightHalf (e : RatExpr 1) : RatExpr 1 :=
  e.substitute (fun _ => .const (1/2)+.const (1/2)*.var 0)

theorem leftHalf_eval (e : RatExpr 1) (t : ℝ) : e.leftHalf.evalOne t=e.evalOne (t/2) := by
  simp only [leftHalf,evalOne,substitute_eval,eval_mulNotation,eval,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  congr 1
  funext i
  ring

theorem rightHalf_eval (e : RatExpr 1) (t : ℝ) : e.rightHalf.evalOne t=e.evalOne ((1+t)/2) := by
  simp only [rightHalf,evalOne,substitute_eval,eval_addNotation,eval_mulNotation,eval,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  congr 1
  funext i
  ring

def midpointSubdividedCheck (scale : ℕ) (e : RatExpr 1) (bound : ℤ) : ℕ→Bool
  | 0 => e.midpointTaylorCleanCheck scale bound
  | n+1 => midpointSubdividedCheck scale e.leftHalf bound n &&
      midpointSubdividedCheck scale e.rightHalf bound n

theorem midpointSubdividedCheck_sound {scale : ℕ} (hs : 0<scale)
    (e : RatExpr 1) (bound : ℤ) (depth : ℕ)
    (hc : e.midpointSubdividedCheck scale bound depth=true) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) : |e.evalOne t|≤(bound:ℝ)/(scale:ℝ) := by
  induction depth generalizing e t with
  | zero => exact midpointTaylorCleanCheck_sound hs e bound hc ht
  | succ n ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    by_cases hhalf : t≤1/2
    · have h := ih e.leftHalf hh.1 (t:=2*t) ⟨by linarith [ht.1],by linarith⟩
      rw [leftHalf_eval,show (2*t)/2=t by ring] at h
      exact h
    · have h := ih e.rightHalf hh.2 (t:=2*t-1) ⟨by linarith,by linarith [ht.2]⟩
      rw [rightHalf_eval,show (1+(2*t-1))/2=t by ring] at h
      exact h

end OptimalG.Certificates.RatExpr
