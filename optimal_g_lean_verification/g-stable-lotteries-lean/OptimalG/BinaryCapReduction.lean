import OptimalG.BinarySplitReduction
import OptimalG.VariationalDefs

/-! Corrected algebra for C.3.  The q=0 constraint is p J(1-p) ≤ λ J(p).
The central-strip residual is the negative of the q-factor displayed in C.14;
this is the orientation used by the accompanying numerical certificate. -/
namespace OptimalG
open Set

theorem binary_cap_complement (lam S p : ℝ) (hp : p ≠ 0) :
    p*Variational.cap lam S (1-p)=lam*(Variational.quadratic lam p-S) := by
  unfold Variational.cap Variational.quadratic
  have he : 1-(1-p)=p := by ring
  rw [he]
  field_simp
  ring

theorem binary_cap_increment (lam S p q : ℝ) (hp : p ≠ 0) (hpq : p-q ≠ 0) :
    Variational.cap lam S (q+1-p)-Variational.cap lam S (1-p)=
      q*(lam/2-lam*S/(p*(p-q))) := by
  unfold Variational.cap
  have he : 1-(1-p)=p := by ring
  have hf : 1-(q+1-p)=p-q := by ring
  rw [he,hf]
  field_simp
  ring

theorem binary_central_slack_identity (lam S p q phi0 slope error : ℝ)
    (hp : p ≠ 0) (hpq : p-q ≠ 0) :
    (lam-q)*(Variational.quadratic lam p-S)-
      p*(Variational.cap lam S (q+1-p)+error-(phi0*q+slope*q^2/2))=
    -q*(Variational.quadratic lam p-S+p*(lam/2-phi0-slope*q/2)-lam*S/(p-q))-p*error := by
  have hc := binary_cap_complement lam S p hp
  have hi := binary_cap_increment lam S p q hp hpq
  have hie := congrArg (fun t : ℝ => p*t) hi
  have hcancel : p*(q*(lam/2-lam*S/(p*(p-q))))=
      p*q*lam/2-q*(lam*S/(p-q)) := by field_simp <;> ring
  rw [hcancel] at hie
  nlinarith only [hc,hie]

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- A retained rational cap proves the last part of the q=0 check. -/
theorem binary_zero_split_of_cap {p S : ℝ} (hp : 0 < p)
    (hflat : curvePrimitive phi p=Variational.quadratic lam p-S)
    (hcap : curvePrimitive phi (1-p) ≤ Variational.cap lam S (1-p)) :
    p*curvePrimitive phi (1-p) ≤ lam*curvePrimitive phi p := by
  rw [hflat,← binary_cap_complement lam S p (ne_of_gt hp)]
  exact mul_le_mul_of_nonneg_left hcap hp.le

/-- The checked central-strip expression is exactly the negative binary slack. -/
theorem binary_central_of_checked_expression {p q S phi0 slope error : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hqp : q < p)
    (hflat : curvePrimitive phi p=Variational.quadratic lam p-S)
    (hhead : curvePrimitive phi q=phi0*q+slope*q^2/2)
    (hcap : curvePrimitive phi (q+1-p) ≤ Variational.cap lam S (q+1-p)+error)
    (hcheck : q*(Variational.quadratic lam p-S+p*(lam/2-phi0-slope*q/2)-lam*S/(p-q))+
      p*error ≤ 0) :
    q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam := by
  have hid := binary_central_slack_identity lam S p q phi0 slope error
    (ne_of_gt hp.1) (sub_ne_zero.mpr (ne_of_gt hqp))
  have hm := mul_le_mul_of_nonneg_left hcap hp.1.le
  have hs : p*(curvePrimitive phi (q+1-p)-curvePrimitive phi q) ≤
      (lam-q)*curvePrimitive phi p := by
    rw [hflat,hhead]
    nlinarith only [hid,hm,hcheck]
  have he : 1-p+q=q+1-p := by ring
  unfold packingDelta
  rw [he]
  have hd : (p/curvePrimitive phi p)*(curvePrimitive phi (q+1-p)-curvePrimitive phi q) ≤ lam-q := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (h.primitive_pos hp)).mpr hs
  linarith

end VerifierCurve
end OptimalG
