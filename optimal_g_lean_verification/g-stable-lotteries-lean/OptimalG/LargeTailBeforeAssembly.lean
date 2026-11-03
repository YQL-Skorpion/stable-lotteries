import OptimalG.LargeTailSplitAnalytic
import OptimalG.LargeMassFlatEnvelope
import OptimalG.TailPrimitiveBox

namespace OptimalG
open Set Variational Certificates.LargeTailExpressions

structure LargeTailSplitSigns (lam S p M z Y H : ℝ) : Prop where
  head_zero : z-p≤527/2000→headLow lam S p M z Y H 0≤0
  head_join : z-p≤527/2000→headLow lam S p M z Y H (527/2000-z+p)≤0
  cap_zero : 527/2000≤z-p→z-p≤313/1000→capCore lam S p M z Y H 0≤0
  cap_join : z-p≤313/1000→capCore lam S p M z Y H (313/1000-z+p)≤0
  head_square : headCleared lam S p M z Y H≤0
  high_cap : highCapCleared lam S p M z Y H≤0
  forward_left : flatHigh lam S p M z Y H (1459/5000) (capDeficit lam S (1459/5000))≤0
  forward_right : flatHigh lam S p M z Y H lam 0≤0
  forward_kink : flatHigh lam S p M z Y H (kink lam S) 0≤0

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

private theorem flat_primitive_upper (h : VerifierCurve phi lam) {r : ℝ}
    (hr : r∈Icc (313/1000:ℝ) 1) :
    curvePrimitive phi r≤quadratic lam r-S+flat lam S := by
  have hh := h.binarySlackArea_antitone S
    (show (313/1000:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    ⟨by linarith only [hr.1],hr.2⟩ hr.1
  have hc := g.cap_upper (313/1000) (by constructor <;> norm_num)
  unfold binarySlackArea flat capDeficit at *
  linarith only [hh,hc]

/-- All low splits for a fixed primitive/anchor corner reduce to explicit
endpoint and completed-square tests. No mixed-test premise is assumed. -/
theorem fixed_large_tail_before_nonpos (h : VerifierCurve phi lam)
    {p M z Y H : ℝ} (hp : p∈Icc (13/20:ℝ) (41/50))
    (hz : z∈Icc (7/8:ℝ) (97/100))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hslope : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (hprod : lam*S≤3/200)
    (harea : 0≤capDeficit lam S (1459/5000))
    (hslack : 0<capSlack lam S (1459/5000))
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hn : LargeTailSplitSigns lam S p M z Y H) :
    ∀ q∈Icc (0:ℝ) lam,
      core lam p M z Y H q (curvePrimitive phi (z-p+q)) (curvePrimitive phi q)≤0 := by
  have hp0 : 0<p := by linarith only [hp.1]
  have head (q : ℝ) (hq : q∈Icc (0:ℝ) (527/2000)) :
      curvePrimitive phi q=Certificates.SmallMassExpressions.primitive lam S q := by
    rw [h.affine_head_primitive g.head hq,hinitial]
    rfl
  intro q hq
  have hr : z-p+q∈Icc (0:ℝ) 1 := by
    constructor <;> linarith only [hz.1,hz.2,hp.1,hp.2,hq.1,hq.2,g.lambda_mem.2]
  by_cases hqh : 527/2000≤q
  · have hru : 313/1000≤z-p+q := by linarith only [hz.1,hp.2,hqh]
    have hupper := g.flat_primitive_upper h ⟨hru,hr.2⟩
    have hlower := g.largeRemainingLower_bound h hq
    by_cases hqw : q≤1459/5000
    · have he : largeRemainingLower lam S (phi 0) (Certificates.SmallMassExpressions.slope lam S) q=
          capDeficit lam S q := by
        by_cases hx : q≤527/2000
        · have hqx : q=527/2000 := le_antisymm hx hqh
          subst q
          rw [largeRemainingLower,if_pos le_rfl,hinitial]
          have hj := head (527/2000) ⟨by norm_num,le_rfl⟩
          have hc := g.cap_primitive (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
          rw [hj] at hc
          unfold Certificates.SmallMassExpressions.primitive at hc
          unfold capDeficit
          linarith only [hc]
        · rw [largeRemainingLower,if_neg hx,if_pos hqw]
      rw [he] at hlower
      have hlow : quadratic lam q-S+capDeficit lam S q≤curvePrimitive phi q := by
        unfold binarySlackArea at hlower
        linarith only [hlower]
      apply (core_mono hp0.le hupper hlow).trans
      rw [flatHigh_identity]
      exact flatHigh_cap_nonpos hp0 hprod ⟨hqh,hqw⟩ hn.high_cap
    · have hx : ¬q≤527/2000 := by linarith only [hqw]
      rw [largeRemainingLower,if_neg hx,if_neg hqw] at hlower
      have hlow : quadratic lam q-S+
          max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000))≤
          curvePrimitive phi q := by
        unfold binarySlackArea at hlower
        linarith only [hlower]
      apply (core_mono hp0.le hupper hlow).trans
      rw [flatHigh_identity]
      exact flatHigh_forward_nonpos hp0.le harea hslack ⟨le_of_not_ge hqw,hq.2⟩
        hn.forward_left hn.forward_right hn.forward_kink
  · have hhead := head q ⟨hq.1,le_of_not_ge hqh⟩
    by_cases hrf : 313/1000≤z-p+q
    · have hupper := g.flat_primitive_upper h ⟨hrf,hr.2⟩
      apply (core_mono hp0.le hupper hhead.ge).trans
      rw [flatHead_identity]
      exact flatHead_nonpos hp0 hslope hn.head_square
    · by_cases hrh : z-p+q≤527/2000
      · have hupper := head (z-p+q) ⟨hr.1,hrh⟩
        rw [hupper,hhead,headLow_identity]
        have hd : z-p≤527/2000 := by linarith only [hrh,hq.1]
        exact headLow_nonpos ⟨hq.1,by linarith only [hrh]⟩ (hn.head_zero hd) (hn.head_join hd)
      · have hupper := g.cap_upper (z-p+q) ⟨hr.1,by linarith only [hrf]⟩
        apply (core_mono hp0.le hupper hhead.ge).trans
        rw [capCore_identity]
        have hd : z-p≤313/1000 := by linarith only [hrf,hq.1]
        have htop := hn.cap_join hd
        by_cases hdh : z-p≤527/2000
        · apply capCore_nonpos hp0.le (a:=527/2000-z+p) (b:=313/1000-z+p)
            (by linarith) (by linarith) ?_ ?_ htop
            ⟨by linarith only [hrh],by linarith only [hrf]⟩
          · intro u hu v hv huv
            have hu' : z-p+u∈Icc (0:ℝ) (9/25) := by constructor <;> linarith only [hu.1,hu.2]
            have hv' : z-p+v∈Icc (0:ℝ) (9/25) := by constructor <;> linarith only [hv.1,hv.2]
            convert! hcapOrder _ hu' _ hv' (by linarith only [huv]) using 1 <;> ring
          · rw [←headLow_cap_join]
            exact hn.head_join hdh
        · apply capCore_nonpos hp0.le (a:=0) (b:=313/1000-z+p)
            (by linarith only [hd]) (by linarith) ?_
            (hn.cap_zero (le_of_not_ge hdh) hd) htop
            ⟨hq.1,by linarith only [hrf]⟩
          intro u hu v hv huv
          have hu' : z-p+u∈Icc (0:ℝ) (9/25) := by constructor <;> linarith only [hdh,hu.1,hu.2]
          have hv' : z-p+v∈Icc (0:ℝ) (9/25) := by constructor <;> linarith only [hdh,hv.1,hv.2]
          convert! hcapOrder _ hu' _ hv' (by linarith only [huv]) using 1 <;> ring

end BinaryCurveGeometry
end OptimalG
