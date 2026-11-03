import OptimalG.Certificates.IntermediateTailExpressions
import OptimalG.IntermediatePrimitiveCorrection
import OptimalG.ExtendedSelectedFiniteTargets

/-! Intermediate-mass tail coverage from ten explicit scalar families.
High initial ranks are affine, the head is controlled by its full square,
and cap-shift ranks use convexity and a triangular endpoint cover. -/
namespace OptimalG
open Set Variational Certificates.IntermediateTailExpressions

/-- Five pure scalar families at one anchor-score endpoint. The two
endpoint values of H give exactly ten families. -/
structure IntermediateTailPolynomialSigns (lam S p H : ℝ) : Prop where
  high : ∀ z∈Icc (7/8:ℝ) 1,
    highCore lam S p z (8793/100000) H (527/2000)≤0 ∧
    highCore lam S p z (8793/100000) H lam≤0
  head : ∀ z∈Icc (7/8:ℝ) 1,headCleared lam S p z (8793/100000) H≤0
  cap : ∀ u∈Icc (0:ℝ) 1,
    let z := 7/8+u*(p-103/200)
    capCore lam S p z (8793/100000) H 0≤0 ∧
    capCore lam S p z (8793/100000) H (9/25-z+p)≤0

noncomputable def intermediateTailEnvelope (phi : ℝ→ℝ) (lam S p z Y H q : ℝ) : ℝ :=
  massFactor lam S p*(z+q-lam)+etaNumerator lam S p*tailScore (539/625) Y H z+
    weight lam S p*(curvePrimitive phi (z-p+q)-tailPrimitive (539/625) Y H z-curvePrimitive phi q)

theorem intermediateTailEnvelope_le {phi : ℝ→ℝ} {lam S p z Y H q upper lower : ℝ}
    (hw : 0≤weight lam S p)
    (hu : curvePrimitive phi (z-p+q)≤upper) (hl : lower≤curvePrimitive phi q) :
    intermediateTailEnvelope phi lam S p z Y H q≤
      massFactor lam S p*(z+q-lam)+etaNumerator lam S p*tailScore (539/625) Y H z+
      weight lam S p*(upper-tailPrimitive (539/625) Y H z-lower) := by
  have hh := mul_le_mul_of_nonneg_left (show curvePrimitive phi (z-p+q)-
      tailPrimitive (539/625) Y H z-curvePrimitive phi q≤
      upper-tailPrimitive (539/625) Y H z-lower by linarith only [hu,hl]) hw
  unfold intermediateTailEnvelope
  linarith only [hh]

theorem intermediate_fixed_anchor_nonpos {phi : ℝ→ℝ} {lam S c p z H : ℝ}
    (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hp : p∈Icc lam (13/20:ℝ)) (hz : z∈Icc (7/8:ℝ) 1)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hF : 0<Certificates.IntermediateTailExpressions.headScore lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hn : IntermediateTailPolynomialSigns lam S p H) :
    ∀ q∈Icc (0:ℝ) lam,intermediateTailEnvelope phi lam S p z (8793/100000) H q≤0 := by
  have hw : 0<weight lam S p := mul_pos (by linarith only [g.lambda_mem.1,hp.1]) hF
  have hs : 0<1+Certificates.SmallMassExpressions.slope lam S := by
    linarith only [g.head_slope]
  have hline := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
  intro q hq
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hz.1,hp.2,hq.1],by linarith only [hz.2,hq.2,hp.1]⟩
  by_cases hqh : 527/2000≤q
  · have hremaining := hline (z-p+q) ⟨by linarith only [hz.1,hp.2,hqh],hr.2⟩
    have hlower : quadratic lam q-S≤curvePrimitive phi q := by
      have hh := h.primitive_relative_quadratic_antitone
        (a:=q) ⟨hq.1,by linarith only [hq.2,g.lambda_mem.2]⟩
        (b:=31/40) (by norm_num) (by linarith only [hq.2,g.lambda_mem.2])
      dsimp only at hh
      rw [g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
      linarith only [hh]
    have he := intermediateTailEnvelope_le (Y:=8793/100000) (H:=H) hw.le hremaining hlower
    rw [←highCore_identity] at he
    exact he.trans (highCore_le_endpoints (hn.high z hz).1 (hn.high z hz).2 q ⟨hqh,hq.2⟩)
  · have hhead : curvePrimitive phi q=Certificates.SmallMassExpressions.primitive lam S q := by
      rw [h.affine_head_primitive g.head ⟨hq.1,le_of_not_ge hqh⟩,hinitial]
      rfl
    by_cases hrl : 9/25≤z-p+q
    · have hremaining := hline (z-p+q) ⟨hrl,hr.2⟩
      have he := intermediateTailEnvelope_le (Y:=8793/100000) (H:=H) hw.le hremaining hhead.ge
      rw [←headCore_identity] at he
      exact he.trans (headCore_nonpos_of_cleared hw hs (hn.head z hz))
    · have hremaining := g.cap_upper (z-p+q) ⟨hr.1,by linarith only [hrl]⟩
      have he := intermediateTailEnvelope_le (Y:=8793/100000) (H:=H) hw.le hremaining hhead.ge
      rw [←capCore_identity] at he
      have harg : z-p≤9/25 := by linarith only [hrl,hq.1]
      obtain ⟨u,hu,hzu⟩ := exists_unit_affine_parameter
        (a:=7/8) (b:=p+9/25) (z:=z) ⟨hz.1,by linarith only [harg]⟩
      have hz' : z=7/8+u*(p-103/200) := by
        calc
          z=7/8+(p+9/25-7/8)*u := hzu
          _=_ := by ring
      have hends : capCore lam S p z (8793/100000) H 0≤0 ∧
          capCore lam S p z (8793/100000) H (9/25-z+p)≤0 := by
        simpa only [←hz'] using hn.cap u hu
      apply he.trans
      apply capCore_le_endpoints hw.le (by linarith only [harg])
        (by linarith : z-p+(9/25-z+p)<1) _ hends.1 hends.2 q
        ⟨hq.1,by linarith only [hrl]⟩
      intro u hu v hv huv
      have hu' : z-p+u∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,hu.1],by linarith only [hu.2]⟩
      have hv' : z-p+v∈Icc (0:ℝ) (9/25) :=
        ⟨by linarith only [hz.1,hp.2,hv.1],by linarith only [hv.2]⟩
      convert! hcapOrder _ hu' _ hv' (by linarith only [huv]) using 1 <;> ring

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The ten scalar sign families give every low-split intermediate tail
test. The actual complementary primitive comes from the .35 area bound. -/
theorem intermediate_tail_of_polynomial_signs {S c p z Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hp : p∈Icc lam (13/20:ℝ)) (hz : z∈Icc (7/8:ℝ) 1)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hF : 0<Certificates.IntermediateTailExpressions.headScore lam S) (hD : 0≤etaNumerator lam S p)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (harea : binarySlackArea phi lam S (7/20)≤87/1000000000)
    (hY : 8793/100000≤Y) (hH : H∈Icc (-(3589/10000):ℝ) (-(1757/5000)))
    (hscore : phi z=tailScore (539/625) Y H z)
    (hprimitive : curvePrimitive phi z=tailPrimitive (539/625) Y H z)
    (hnlo : IntermediateTailPolynomialSigns lam S p (-(3589/10000)))
    (hnhi : IntermediateTailPolynomialSigns lam S p (-(1757/5000))) :
    ∀ q∈Icc (0:ℝ) lam,z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam (527/2000) p*phi z≤0 := by
  have hp01 : p∈Ioo (0:ℝ) 1 :=
    ⟨by linarith only [hp.1,g.lambda_mem.1],by linarith only [hp.2]⟩
  have hR := g.line_primitive p
    ⟨by linarith only [hp.1,g.lambda_mem.1],by linarith only [hp.2]⟩
  have hFactual : phi (527/2000)=Certificates.IntermediateTailExpressions.headScore lam S :=
    g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  have hP : curvePrimitive phi (1-p)≤complementUpper lam S p :=
    h.intermediate_complement_primitive_upper ⟨hp01.1.le,hp.2⟩ harea
  have hnegative : phi z≤0 := by
    have hh := h.ceiling z ⟨by linarith only [hz.1],hz.2⟩
    linarith only [hh,g.lambda_mem.2,hz.1]
  intro q hq
  have hlo := intermediate_fixed_anchor_nonpos h g hp hz hinitial hF hcapOrder hnlo q hq
  have hhi := intermediate_fixed_anchor_nonpos h g hp hz hinitial hF hcapOrder hnhi q hq
  apply h.intermediate_tail_of_primitive_bounds
    (a:=539/625) (upper:=curvePrimitive phi (z-p+q)) (lower:=curvePrimitive phi q)
    (Ylo:=8793/100000) (Hlo:=-(3589/10000)) (Hhi:=-(1757/5000))
    (by norm_num) hp01 ⟨by linarith only [hz.1],hz.2⟩
    (hFactual.symm ▸ hF) hnegative hP le_rfl le_rfl hY hH hscore hprimitive
  · simpa only [hR,hFactual,etaNumerator,massFactor,massPrimitive] using hD
  · simpa only [intermediateTailEnvelope,hR,hFactual,etaNumerator,massFactor,massPrimitive,weight] using hlo
  · simpa only [intermediateTailEnvelope,hR,hFactual,etaNumerator,massFactor,massPrimitive,weight] using hhi

end VerifierCurve
end OptimalG
