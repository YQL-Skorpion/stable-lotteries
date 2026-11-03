import OptimalG.MiddleRankConvexity
import OptimalG.PolynomialCompletion

/-! A nonnegative derivative propagates the actual binary endpoint test
backwards along a polynomial tail. No coefficient normalization is used. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem mixed_tail_of_nonnegative_derivative {p q beta cut a Y H : ℝ}
    (hp : p∈Ioo (0:ℝ) 1) (hq : q∈Icc (0:ℝ) p)
    (hscore : ∀ r∈Icc cut 1,phi r=tailScore a Y H r)
    (hderivative : ∀ r∈Icc (max p cut) 1,
      0≤1+beta*(phi (r-p+q)-phi r)+tailSlope a Y H r)
    (hbinary : q+beta*packingDelta phi p q≤lam) :
    ∀ z∈Icc (max p cut) 1,z+q-lam+beta*packingK phi p q z+phi z≤0 := by
  intro z hz
  let start := max p cut
  have hpstart : p≤start := le_max_left _ _
  have hcstart : cut≤start := le_max_right _ _
  have hstart1 : start≤1 := hz.1.trans hz.2
  have hstart0 : 0≤start := hp.1.le.trans hpstart
  let G : ℝ→ℝ := fun r=>r+q-lam+beta*packingK phi p q r+tailScore a Y H r
  have hcomp : ContinuousOn (fun r=>curvePrimitive phi (r-p+q)) (Icc start 1) := by
    apply h.primitive_continuous.comp ((continuous_id.sub continuous_const).add continuous_const).continuousOn
    intro r hr
    change 0≤r-p+q ∧ r-p+q≤1
    constructor <;> linarith only [hpstart,hr.1,hr.2,hq.1,hq.2]
  have hJ : ContinuousOn (curvePrimitive phi) (Icc start 1) :=
    h.primitive_continuous.mono (Icc_subset_Icc hstart0 le_rfl)
  have htail := (tailScore_continuous a Y H).continuousOn (s:=Icc start 1)
  have hcont : ContinuousOn G (Icc start 1) := by
    dsimp [G,packingK]
    fun_prop
  have hd (r : ℝ) (hr : r∈interior (Icc start 1)) :
      HasDerivAt G (1+beta*(phi (r-p+q)-phi r)+tailSlope a Y H r) r := by
    rw [interior_Icc] at hr
    have hsarg : r-p+q∈Ioo (0:ℝ) 1 :=
      ⟨by linarith only [hpstart,hr.1,hq.1],by linarith only [hr.2,hq.2]⟩
    have hrarg : r∈Ioo (0:ℝ) 1 := ⟨hstart0.trans_lt hr.1,hr.2⟩
    have hs := (h.primitive_hasDerivAt hsarg).comp r
      (((hasDerivAt_id r).sub_const p).add_const q)
    have hj := h.primitive_hasDerivAt hrarg
    have hh := ((((hasDerivAt_id r).add_const q).sub_const lam).add
      (((hs.sub hj).sub_const (curvePrimitive phi q)).const_mul beta)).add
      (tailScore_hasDerivAt a Y H r)
    convert! hh using 1 <;> first | rfl | (simp only [id_eq,mul_one] <;> ring)
  have hmono : MonotoneOn G (Icc start 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc start 1) hcont
    · intro r hr
      exact (hd r hr).hasDerivWithinAt
    · intro r hr
      exact hderivative r (interior_subset hr)
  have hG1 : G 1≤0 := by
    have hJ1 : curvePrimitive phi 1=0 := h.integral_zero
    have hphi1 := hscore 1 ⟨hcstart.trans hstart1,le_rfl⟩
    dsimp [G]
    rw [←hphi1,h.at_one]
    simp only [packingK,hJ1,sub_zero]
    unfold packingDelta at hbinary
    linarith only [hbinary]
  have hh := (hmono hz ⟨hstart1,le_rfl⟩ hz.2).trans hG1
  dsimp [G] at hh
  rw [←hscore z ⟨hcstart.trans hz.1,hz.2⟩] at hh
  exact hh

end VerifierCurve
end OptimalG
