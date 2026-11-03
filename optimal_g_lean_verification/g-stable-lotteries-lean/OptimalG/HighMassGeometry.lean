import OptimalG.ConstantCorrection
import OptimalG.LargeMassEnd
import OptimalG.BinarySplitReduction

/-! Analytic inputs to C.5. The only scalar inequalities below are explicitly
identified coefficient or finite-box inputs; no high-mass verifier is assumed. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def intermediateCorrection (phi : ℝ → ℝ) (lam p : ℝ) : ℝ :=
  lam - (p / curvePrimitive phi p) * curvePrimitive phi (1-p)
noncomputable def intermediateEta (phi : ℝ → ℝ) (lam xh p : ℝ) : ℝ :=
  1 + intermediateCorrection phi lam p / phi xh

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- An affine initial score segment reduces the extra intermediate correction
ratio to its left endpoint. The right endpoint follows from the score ceiling. -/
theorem constantCorrection_eta_bound {xh slope c : ℝ}
    (hxh : xh ∈ Ioo (0 : ℝ) lam) (hc : 0 ≤ c)
    (haff : ∀ x ∈ Icc (0 : ℝ) xh, phi x = phi 0 + slope*x)
    (hzero : (1+c/phi xh)*phi 0 ≤ lam+c) :
    ∀ x ∈ Ico (0 : ℝ) lam,
      1+c/phi xh ≤ lowRankRatio phi lam x + correctionRatio phi c x := by
  have hf := h.positive ⟨hxh.1.le,hxh.2⟩
  have hright : (1+c/phi xh)*phi xh ≤ lam-xh+c := by
    have hceil := h.ceiling xh ⟨hxh.1.le,hxh.2.le.trans h.lam_lt_one.le⟩
    rw [add_mul,one_mul,div_mul_cancel₀ c hf.ne']
    linarith
  intro x hx
  unfold lowRankRatio correctionRatio
  rw [← add_div,le_div_iff₀ (h.positive hx)]
  by_cases hxx : x ≤ xh
  · have h0 := mul_le_mul_of_nonneg_left hzero (sub_nonneg.mpr hxx)
    have hh := mul_le_mul_of_nonneg_left hright hx.1
    nth_rw 2 [haff xh ⟨hxh.1.le,le_rfl⟩] at hh
    rw [haff x ⟨hx.1,hxx⟩]
    apply (mul_le_mul_iff_right₀ hxh.1).mp
    nlinarith only [h0,hh]
  · have hanti := h.decreasing.antitoneOn
      ⟨hxh.1.le,hxh.2.le.trans h.lam_lt_one.le⟩
      ⟨hx.1,hx.2.le.trans h.lam_lt_one.le⟩ (le_of_not_ge hxx)
    have hcphi := mul_le_mul_of_nonneg_left hanti (div_nonneg hc hf.le)
    rw [div_mul_cancel₀ c hf.ne'] at hcphi
    have hceil := h.ceiling x ⟨hx.1,hx.2.le.trans h.lam_lt_one.le⟩
    nlinarith only [hcphi,hceil]

/-- The straight middle segment is convex also when the mass itself exceeds λ. -/
theorem highMass_middle_convex {p q beta eta z0 : ℝ}
    (hp : lam ≤ p) (hq : q ∈ Icc (0 : ℝ) lam)
    (hpz : p ≤ z0) (hz01 : z0 ≤ 1) (hb : 0 ≤ beta)
    (hline : ∀ z ∈ Icc lam z0, phi z = lam-z)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ z0 → a-b ≤ phi b-phi a) :
    ConvexOn ℝ (Icc p z0)
      (fun z => z+q-lam+beta*packingK phi p q z+eta*phi z) := by
  let G := fun z => z+q-lam+beta*packingK phi p q z+eta*(lam-z)
  have hcomp : ContinuousOn (fun z => curvePrimitive phi (z-p+q)) (Icc p z0) := by
    apply h.primitive_continuous.comp ((continuous_id.sub continuous_const).add continuous_const).continuousOn
    intro z hz
    change 0 ≤ z-p+q ∧ z-p+q ≤ 1
    constructor <;> linarith [hz.1,hz.2,hq.1,hq.2]
  have hJ : ContinuousOn (curvePrimitive phi) (Icc p z0) :=
    h.primitive_continuous.mono (Icc_subset_Icc (h.lam_pos.le.trans hp) hz01)
  have hcont : ContinuousOn G (Icc p z0) := by dsimp [G,packingK]; fun_prop
  have hderiv (z : ℝ) (hz : z ∈ interior (Icc p z0)) :
      HasDerivAt G (1-eta+beta*(phi (z-p+q)+z-lam)) z := by
    rw [interior_Icc] at hz
    have hsarg : z-p+q ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hz.1,hq.1],by linarith [hz.2,hq.2]⟩
    have hzarg : z ∈ Ioo (0:ℝ) 1 := ⟨by linarith [h.lam_pos,hz.1],hz.2.trans_le hz01⟩
    have hs := (h.primitive_hasDerivAt hsarg).comp z (((hasDerivAt_id z).sub_const p).add_const q)
    have hj := h.primitive_hasDerivAt hzarg
    have hd := ((((hasDerivAt_id z).add_const q).sub_const lam).add
      (((hs.sub hj).sub_const (curvePrimitive phi q)).const_mul beta)).add
      (((hasDerivAt_const z lam).sub (hasDerivAt_id z)).const_mul eta)
    have hl := hline z ⟨hp.trans hz.1.le,hz.2.le⟩
    convert! hd using 1 <;> first | rfl | (simp only [id_eq,mul_one,zero_sub,hl]; ring)
  have hconv : ConvexOn ℝ (Icc p z0) G := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc p z0) hcont
      (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    intro a ha b hb' hab
    rw [(hderiv a ha).deriv,(hderiv b hb').deriv]
    rw [interior_Icc] at ha hb'
    have hh := hfall (a-p+q) (b-p+q) (by linarith [ha.1,hq.1])
      (by linarith) (by linarith [hb'.2,hq.2])
    have hm := mul_nonneg hb (show 0 ≤ (phi (b-p+q)+b-lam)-(phi (a-p+q)+a-lam) by linarith)
    linarith
  apply hconv.congr
  intro z hz
  dsimp [G]
  rw [hline z ⟨hp.trans hz.1,hz.2⟩]

/-- For a normalized positive coefficient, the mass endpoint is automatic;
only the high endpoint of the middle segment needs a certificate. -/
theorem highMass_middle_of_endpoint {p q beta eta z0 : ℝ}
    (hp : lam ≤ p) (hq : q ∈ Icc (0 : ℝ) lam)
    (hpz : p ≤ z0) (hz01 : z0 ≤ 1) (hb : 0 ≤ beta) (he : 0 ≤ eta)
    (hn : beta*curvePrimitive phi p=p)
    (hline : ∀ z ∈ Icc lam z0, phi z=lam-z)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ z0 → a-b ≤ phi b-phi a)
    (hend : z0+q-lam+beta*packingK phi p q z0+eta*phi z0 ≤ 0) :
    ∀ z ∈ Icc p z0, z+q-lam+beta*packingK phi p q z+eta*phi z ≤ 0 := by
  have hstart : p+q-lam+beta*packingK phi p q p+eta*phi p ≤ 0 := by
    have hk : packingK phi p q p = -curvePrimitive phi p := by simp [packingK]
    rw [hk,mul_neg,hn,hline p ⟨hp,hpz⟩]
    have hm := mul_nonpos_of_nonneg_of_nonpos he (sub_nonpos.mpr hp)
    linarith [hq.2]
  intro z hz
  exact ((h.highMass_middle_convex hp hq hpz hz01 hb hline hfall).le_max_of_mem_Icc
    (left_mem_Icc.mpr hpz) (right_mem_Icc.mpr hpz) hz).trans (max_le hstart hend)

omit h in
private theorem tail_line_integral (M p : ℝ) :
    (∫ u in p..1, -1+M*(1-u)) = -(1-p)+M*(1-p)^2/2 := by
  let F := fun u : ℝ => -u-M*(1-u)^2/2
  have hd (u : ℝ) : HasDerivAt F (-1+M*(1-u)) u := by
    convert! (hasDerivAt_id u).neg.sub
      ((((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).pow 2).const_mul M |>.div_const 2) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply,id_eq,zero_sub,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => -1+M*(1-u))).intervalIntegrable p 1)]
  dsimp [F]
  ring

/-- Integrating an endpoint slope cone gives the actual primitive bound. -/
theorem primitive_tail_cones {p m M : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hcone : ∀ u ∈ Icc p 1, -1+m*(1-u) ≤ phi u ∧ phi u ≤ -1+M*(1-u)) :
    (1-p)-M*(1-p)^2/2 ≤ curvePrimitive phi p ∧
      curvePrimitive phi p ≤ (1-p)-m*(1-p)^2/2 := by
  have hi := h.integral_subinterval hp.1 hp.2 le_rfl
  have hl := intervalIntegral.integral_mono_on hp.2
    ((by fun_prop : Continuous (fun u : ℝ => -1+m*(1-u))).intervalIntegrable p 1)
    hi (fun u hu => (hcone u hu).1)
  have hu := intervalIntegral.integral_mono_on hp.2 hi
    ((by fun_prop : Continuous (fun u : ℝ => -1+M*(1-u))).intervalIntegrable p 1)
    (fun u hu => (hcone u hu).2)
  rw [tail_line_integral] at hl hu
  rw [← h.primitive_difference hp.1 hp.2 le_rfl] at hl hu
  have hzero : curvePrimitive phi 1=0 := h.integral_zero
  rw [hzero] at hl hu
  constructor <;> linarith

/-- The tail slope interval [-6.7,-2] implies precisely the two coefficient
bounds used for the clipped short-split argument. -/
theorem highMass_tail_coefficient {p : ℝ} (hp : p ∈ Ico (22/25:ℝ) 1)
    (hcone : ∀ u ∈ Icc p 1,
      -1+2*(1-u) ≤ phi u ∧ phi u ≤ -1+(67/10)*(1-u)) :
    1 ≤ (p/curvePrimitive phi p)*(1-p) ∧
    (p/curvePrimitive phi p)*(1-p) ≤ p/(1-67*(1-p)/20) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hJ := h.primitive_pos ⟨hp0,hp.2⟩
  have hh : 0 < 1-p := sub_pos.mpr hp.2
  have hd : 0 < 1-67*(1-p)/20 := by linarith [hp.1]
  have hbounds := h.primitive_tail_cones ⟨hp0.le,hp.2.le⟩ hcone
  constructor
  · rw [div_mul_eq_mul_div,le_div_iff₀ hJ]
    nlinarith [hbounds.2]
  · rw [div_mul_eq_mul_div,div_le_div_iff₀ hJ hd]
    have hm := mul_le_mul_of_nonneg_left hbounds.1 hp0.le
    nlinarith only [hm]

end VerifierCurve

/-- Three scalar tail-coefficient bounds imply the entire endpoint cone needed
by C.5. This specializes the cone input to the actual quadratic completion. -/
theorem polynomial_tail_cones {z Y H : ℝ} (hz : z ≠ 1)
    (hk : 0 ≤ tailBackwardCurvature z Y H)
    (hv : tailBackwardSlope z Y H ≤ 67/10)
    (hl : 2 ≤ tailBackwardSlope z Y H-(3/25)*tailBackwardCurvature z Y H) :
    ∀ u ∈ Icc (22/25:ℝ) 1,
      -1+2*(1-u) ≤ tailScore z Y H u ∧
      tailScore z Y H u ≤ -1+(67/10)*(1-u) := by
  intro u hu
  have hh : 0 ≤ 1-u := sub_nonneg.mpr hu.2
  have hhmax : 1-u ≤ 3/25 := by linarith [hu.1]
  rw [tailScore_backward z Y H u hz]
  have hku := mul_le_mul_of_nonneg_left hhmax hk
  have hlo := mul_le_mul_of_nonneg_right
    (show 2 ≤ tailBackwardSlope z Y H-tailBackwardCurvature z Y H*(1-u) by nlinarith only [hl,hku]) hh
  have hhi := mul_le_mul_of_nonneg_right hv hh
  have hk2 := mul_nonneg hk (sq_nonneg (1-u))
  constructor <;> nlinarith only [hlo,hhi,hk2]

end OptimalG
