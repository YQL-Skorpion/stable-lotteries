import OptimalG.Certificates.IntermediateSelectedExpressions
import OptimalG.IntermediatePrimitiveCorrection
import OptimalG.IntermediateTailCoefficientBounds

/-! All-split coverage of the intermediate-mass selected-high strip.
The eight inputs are explicit scalar expressions. Convexity, the cap
curvature remainder and the forward-area kink cover their full rank ranges. -/
namespace OptimalG
open Set Variational
open Certificates.IntermediateTailExpressions (massFactor weight etaNumerator massPrimitive complementUpper)
open Certificates.IntermediateSelectedExpressions

/-- Eight scalar signs at the specified parameters and score-deficit bound. -/
structure IntermediateSelectedSigns (lam S p z e : ℝ) : Prop where
  coefficient : 0≤deficitCoefficient lam S p z
  capZero : capCore lam S p z e 0≤0
  capBoundary : capCore lam S p z e (9/25-z+p)≤0
  head : headCleared lam S p z e≤0
  cap : capCleared lam S p z e≤0
  forwardLeft : highCore lam S p z e (1459/5000) (capDeficit lam S (1459/5000))≤0
  forwardKink : highCore lam S p z e (kink lam S) 0≤0
  forwardRight : highCore lam S p z e lam 0≤0

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The primitive triangle estimate and the sign of its coefficient justify
replacing the actual score deficit by a proved lower bound. -/
theorem intermediate_selected_primitive_reduction {S p q z e upper lower : ℝ}
    (hp : p∈Ioo (0:ℝ) 1)
    (hR : curvePrimitive phi p=massPrimitive lam S p)
    (hF : phi (527/2000)=Certificates.IntermediateTailExpressions.headScore lam S)
    (hFpos : 0<Certificates.IntermediateTailExpressions.headScore lam S)
    (hzscore : phi z≤0)
    (hP : curvePrimitive phi (1-p)≤complementUpper lam S p)
    (hupper : curvePrimitive phi (z-p+q)≤upper) (hlower : lower≤curvePrimitive phi q)
    (htriangle : primitiveDefect phi lam S z≤(z-391/500)*scoreDefect phi lam z/2)
    (hdef : e≤scoreDefect phi lam z)
    (hcoef : 0≤deficitCoefficient lam S p z)
    (hc : core lam S p z e q upper lower≤0) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam (527/2000) p*phi z≤0 := by
  apply h.intermediate_mixed_of_primitive_bounds hp (hF.symm ▸ hFpos) hzscore hP hupper hlower
  have hh := mul_le_mul_of_nonneg_left htriangle
    (show 0≤weight lam S p from mul_nonneg hp.1.le hFpos.le)
  have he := (core_antitone_deficit hcoef hdef (q:=q) (upper:=upper) (lower:=lower)).trans hc
  rw [hR,hF]
  simp only [core,primitiveDefect,scoreDefect] at he hh
  dsimp only [massFactor,weight,etaNumerator] at he hh ⊢
  nlinarith only [he,hh]

/-- Genuine all-rank mixed tests on [.782,.875], conditional only on the
explicit scalar signs, the actual curve geometry and a score-deficit lower
bound. The cap and forward sign prerequisites follow from these data. -/
theorem intermediate_selected_of_signs {S c p z e : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc lam (13/20:ℝ)) (hz : z∈Icc (391/500:ℝ) (7/8))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hstart : curvePrimitive phi (391/500)=quadratic lam (391/500)-S)
    (hzero : phi (391/500)=lam-391/500)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hdef : e≤scoreDefect phi lam z) (hn : IntermediateSelectedSigns lam S p z e) :
    ∀ q∈Icc (0:ℝ) lam,z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam (527/2000) p*phi z≤0 := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hF := (intermediate_tail_coefficient_signs hL hS hp).1
  have hw : 0<weight lam S p := mul_pos (by linarith only [g.lambda_mem.1,hp.1]) hF
  have hs : 0<1+Certificates.SmallMassExpressions.slope lam S := by linarith only [g.head_slope]
  have hp01 : p∈Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩
  have hR := g.line_primitive p ⟨by linarith only [hp.1,hL.1],by linarith only [hp.2]⟩
  have hFactual : phi (527/2000)=Certificates.IntermediateTailExpressions.headScore lam S :=
    g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  have hP : curvePrimitive phi (1-p)≤complementUpper lam S p :=
    h.intermediate_complement_primitive_upper ⟨hp01.1.le,hp.2⟩ harea
  have hnegative : phi z≤0 := by
    have hh := h.ceiling z ⟨by linarith only [hz.1],by linarith only [hz.2]⟩
    linarith only [hh,hL.2,hz.1]
  have htriangle := h.primitiveDefect_le_triangle hc
    (by linarith only [hL.2] : lam≤391/500) hz.1 (by linarith only [hz.2]) hstart hzero
  have hline := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
  have hprod : lam*S≤3/200 := by
    have hh := mul_le_mul hL.2 hS.2 (by linarith only [hS.1]) (by norm_num : (0:ℝ)≤56233/100000)
    norm_num at hh ⊢
    linarith only [hh]
  have hslack : 0<capSlack lam S (1459/5000) := by
    have hh := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
      (by linarith only [hL.1] : 0≤lam)
    unfold capSlack capScore
    norm_num
    nlinarith only [hh,hL.1]
  have hE : 0≤capDeficit lam S (1459/5000) := by
    have hh := h.primitive_relative_quadratic_antitone
      (a:=1459/5000) (by norm_num) (b:=31/40) (by norm_num) (by norm_num)
    dsimp only at hh
    rw [g.cap_primitive (1459/5000) ⟨by norm_num,g.contact_mem.1⟩,
      g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
    unfold capDeficit
    linarith only [hh]
  intro q hq
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hz.1,hp.2,hq.1],by linarith only [hz.2,hq.2,hp.1]⟩
  have reduce {upper lower : ℝ} (hu : curvePrimitive phi (z-p+q)≤upper)
      (hl : lower≤curvePrimitive phi q) (ht : core lam S p z e q upper lower≤0) :=
    h.intermediate_selected_primitive_reduction hp01 hR hFactual hF hnegative hP hu hl htriangle hdef hn.coefficient ht
  by_cases hqh : 527/2000≤q
  · have hu := hline (z-p+q) ⟨by linarith only [hz.1,hp.2,hqh],hr.2⟩
    by_cases hqw : q≤1459/5000
    · have hl : quadratic lam q-S+capDeficit lam S q≤curvePrimitive phi q := by
        rw [g.cap_primitive q ⟨hqh,hqw.trans g.contact_mem.1⟩]
        unfold capDeficit
        linarith
      apply reduce hu hl
      rw [←highCore_identity]
      exact highCore_cap_nonpos hw hprod ⟨hqh,hqw⟩ hn.cap
    · have hh := g.slackUpper_bound h hq
      rw [extendedSlackUpper,if_neg (by linarith only [hqw] : ¬q≤527/2000),if_neg hqw] at hh
      have hl : quadratic lam q-S+
          max 0 (capDeficit lam S (1459/5000)-capSlack lam S (1459/5000)*(q-1459/5000))≤curvePrimitive phi q := by
        linarith only [hh]
      apply reduce hu hl
      rw [←highCore_identity]
      exact highCore_forward_nonpos hw.le hE hslack ⟨le_of_not_ge hqw,hq.2⟩
        hn.forwardLeft hn.forwardRight hn.forwardKink
  · have hhead : curvePrimitive phi q=Certificates.SmallMassExpressions.primitive lam S q := by
      rw [h.affine_head_primitive g.head ⟨hq.1,le_of_not_ge hqh⟩,hinitial]
      rfl
    by_cases hrl : 9/25≤z-p+q
    · apply reduce (hline (z-p+q) ⟨hrl,hr.2⟩) hhead.ge
      rw [←headCore_identity]
      exact headCore_nonpos hw hs hn.head
    · apply reduce (g.cap_upper (z-p+q) ⟨hr.1,by linarith only [hrl]⟩) hhead.ge
      change capCore lam S p z e q≤0
      apply capCore_le_endpoints hw.le (by linarith only [hrl,hq.1] : 0≤9/25-z+p)
        (by linarith : z-p+(9/25-z+p)<1) _ hn.capZero hn.capBoundary q
        ⟨hq.1,by linarith only [hrl]⟩
      intro u hu v hv huv
      have hu' : z-p+u∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,hu.1],by linarith only [hu.2]⟩
      have hv' : z-p+v∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,hv.1],by linarith only [hv.2]⟩
      convert! hcapOrder _ hu' _ hv' (by linarith only [huv]) using 1 <;> ring

end VerifierCurve
end OptimalG
