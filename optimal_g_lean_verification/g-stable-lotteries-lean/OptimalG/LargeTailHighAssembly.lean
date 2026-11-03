import OptimalG.LargeTailSplitAnalytic
import OptimalG.LargeMassFlatEnvelope

namespace OptimalG
open Set Variational Certificates.LargeTailExpressions

structure LargeTailHighSigns (lam S p M z Y H : ℝ) : Prop where
  cap : highCapCleared lam S p M z Y H≤0
  left : flatHigh lam S p M z Y H (1459/5000) (capDeficit lam S (1459/5000))≤0
  right : flatHigh lam S p M z Y H lam 0≤0
  kink : flatHigh lam S p M z Y H (Certificates.LargeTailExpressions.kink lam S) 0≤0

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

theorem fixed_large_tail_high_nonpos (h : VerifierCurve phi lam)
    {p M z Y H q : ℝ} (hp : p∈Icc (13/20:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) 1) (hq : q∈Icc (527/2000:ℝ) lam)
    (hprod : lam*S≤3/200) (harea : 0≤capDeficit lam S (1459/5000))
    (hslack : 0<capSlack lam S (1459/5000))
    (hn : LargeTailHighSigns lam S p M z Y H) :
    core lam p M z Y H q (curvePrimitive phi (z-p+q)) (curvePrimitive phi q)≤0 := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hr : z-p+q∈Icc (313/1000:ℝ) 1 := by
    constructor <;> linarith only [hp.1,hp.2,hz.1,hz.2,hq.1,hq.2,g.lambda_mem.2]
  have hu : curvePrimitive phi (z-p+q)≤quadratic lam (z-p+q)-S+flat lam S := by
    have hh := h.binarySlackArea_antitone S
      (show (313/1000:ℝ)∈Icc 0 1 by constructor <;> norm_num)
      ⟨by linarith only [hr.1],hr.2⟩ hr.1
    have hc := g.cap_upper (313/1000) (by constructor <;> norm_num)
    unfold binarySlackArea flat capDeficit at *
    linarith only [hh,hc]
  by_cases hqw : q≤1459/5000
  · have hc := g.cap_primitive q ⟨hq.1,hqw.trans g.contact_mem.1⟩
    have hl : quadratic lam q-S+capDeficit lam S q≤curvePrimitive phi q := by
      rw [hc]
      unfold capDeficit
      linarith
    apply (core_mono hp0.le hu hl).trans
    rw [flatHigh_identity]
    exact flatHigh_cap_nonpos hp0 hprod ⟨hq.1,hqw⟩ hn.cap
  · have hh := g.largeRemainingLower_bound h ⟨by linarith only [hq.1],hq.2⟩
    have hxh : ¬q≤527/2000 := by linarith only [hqw]
    rw [largeRemainingLower,if_neg hxh,if_neg hqw] at hh
    have hl : quadratic lam q-S+
        max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000))≤
        curvePrimitive phi q := by
      unfold binarySlackArea at hh
      linarith only [hh]
    apply (core_mono hp0.le hu hl).trans
    rw [flatHigh_identity]
    exact flatHigh_forward_nonpos hp0.le harea hslack ⟨le_of_not_ge hqw,hq.2⟩
      hn.left hn.right hn.kink

end BinaryCurveGeometry
end OptimalG
