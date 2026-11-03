import OptimalG.ExtendedTailAnalytic
import OptimalG.ExtendedSelectedFiniteTargets

/-! The direct fixed-anchor tail test reduces to twelve explicit polynomial
families. The actual low primitive is bounded by its head, cap and middle
expressions; no mixed-test inequality is assumed in these numerical inputs. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions
open Certificates.ExtendedSelectedExpressions (headLinear)
open Certificates.ExtendedTailExpressions

structure ExtendedTailPolynomialSigns (lam S p t H : ℝ) : Prop where
  head_active : 9/20≤p→∀ z∈Icc (7/8:ℝ) 1,headCleared lam S p t z (8793/100000) H≤0
  head_inactive : p≤9/20→∀ z∈Icc (7/8:ℝ) 1,base lam S p t z (8793/100000) H≤0
  linear_inactive : p≤9/20→headLinear lam S p t (7/8)≤0
  high : ∀ z∈Icc (7/8:ℝ) 1,
    highCore lam S p t z (8793/100000) H (527/2000)≤0 ∧
    highCore lam S p t z (8793/100000) H p≤0
  cap : 103/200≤p→∀ u∈Icc (0:ℝ) 1,
    let z := 7/8+u*(p-103/200)
    capCoreCleared lam S p t z (8793/100000) H 0≤0 ∧
    capCoreCleared lam S p t z (8793/100000) H (9/25-z+p)≤0

theorem fixed_anchor_tail_envelope_nonpos {phi : ℝ→ℝ} {lam S c p t z H : ℝ}
    (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hp : p∈Icc (19/50:ℝ) lam) (hz : z∈Icc (7/8:ℝ) 1)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hJ : 0<betaNumerator lam p t) (hs : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (hn : ExtendedTailPolynomialSigns lam S p t H) :
    ∀ q∈Icc (0:ℝ) p,extendedTailEnvelope phi lam S p t z (8793/100000) H q≤0 := by
  have hline := h.primitive_le_quadratic_after_anchor (a:=9/25) (by norm_num)
    (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
  intro q hq
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hq.1],by linarith only [hz.2,hq.2]⟩
  by_cases hqh : 527/2000≤q
  · have hslack : quadratic lam q-curvePrimitive phi q≤S := by
      have hh := h.primitive_relative_quadratic_antitone
        (a:=q) ⟨hq.1,by linarith only [hq.2,hp.2,g.lambda_mem.2]⟩
        (b:=31/40) (by norm_num) (by linarith only [hq.2,hp.2,g.lambda_mem.2])
      dsimp only at hh
      rw [g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩] at hh
      linarith only [hh]
    have hremaining := hline (z-p+q) ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hqh],hr.2⟩
    have he := extendedTailEnvelope_le_slacks (Y:=8793/100000) (H:=H) hJ.le hslack
      (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤0 by linarith only [hremaining])
    have hb := extended_tail_high_le_endpoints (hn.high z hz).1 (hn.high z hz).2 q ⟨hqh,hq.2⟩
    exact he.trans (by simpa only [highCore,add_zero] using hb)
  · have hhead : curvePrimitive phi q=Certificates.SmallMassExpressions.primitive lam S q := by
      rw [h.affine_head_primitive g.head ⟨hq.1,le_of_not_ge hqh⟩,hinitial]
      rfl
    have hslack : quadratic lam q-curvePrimitive phi q≤
        quadratic lam q-Certificates.SmallMassExpressions.primitive lam S q := by rw [hhead]
    by_cases hrl : 9/25≤z-p+q
    · have hremaining := hline (z-p+q) ⟨hrl,hr.2⟩
      have he := extendedTailEnvelope_le_slacks (Y:=8793/100000) (H:=H) hJ.le hslack
        (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤0 by linarith only [hremaining])
      apply he.trans
      simp only [add_zero]
      rw [←headCore_identity]
      by_cases hp45 : p≤9/20
      · exact extended_tail_head_inactive hJ.le hs.le hq.1 hz.1
          (hn.linear_inactive hp45) (hn.head_inactive hp45 z hz)
      · exact headCore_nonpos_of_cleared hJ hs (hn.head_active (le_of_not_ge hp45) z hz)
    · have hremaining := g.cap_upper (z-p+q) ⟨hr.1,by linarith only [hrl]⟩
      have he := extendedTailEnvelope_le_slacks (Y:=8793/100000) (H:=H) hJ.le hslack
        (show curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤
          cap lam S (z-p+q)-quadratic lam (z-p+q)+S by linarith only [hremaining])
      have harg : z-p≤9/25 := by linarith only [hrl,hq.1]
      have hp515 : 103/200≤p := by linarith only [hz.1,harg]
      obtain ⟨u,hu,hzu⟩ := exists_unit_affine_parameter
        (a:=7/8) (b:=p+9/25) (z:=z) ⟨hz.1,by linarith only [harg]⟩
      have hz' : z=7/8+u*(p-103/200) := by
        calc
          z=7/8+(p+9/25-7/8)*u := hzu
          _=_ := by ring
      have hends : capCoreCleared lam S p t z (8793/100000) H 0≤0 ∧
          capCoreCleared lam S p t z (8793/100000) H (9/25-z+p)≤0 := by
        simpa only [←hz'] using hn.cap hp515 u hu
      have ha := capCore_nonpos_of_cleared (by linarith only [harg]) hends.1
      have hb := capCore_nonpos_of_cleared (by linarith) hends.2
      have hbound : capCore lam S p t z (8793/100000) H q≤0 := by
        apply extended_tail_cap_le_endpoints hJ.le (by linarith only [harg])
          (by linarith : z-p+(9/25-z+p)<1) _ ha hb q ⟨hq.1,by linarith only [hrl]⟩
        intro u hu v hv huv
        have hu' : z-p+u∈Icc (0:ℝ) (9/25) :=
          ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hu.1],by linarith only [hu.2]⟩
        have hv' : z-p+v∈Icc (0:ℝ) (9/25) :=
          ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hv.1],by linarith only [hv.2]⟩
        convert! hcapOrder _ hu' _ hv' (by linarith only [huv]) using 1 <;> ring
      apply he.trans
      convert! hbound using 1 <;> rw [capCore,headCore_identity] <;> ring

/-- Height monotonicity and the two anchor-score endpoints turn the direct
polynomial checks into the actual mixed test on the whole retained tail. -/
theorem extended_tail_high_of_polynomial_signs {phi : ℝ→ℝ} {lam S c p t z Y H : ℝ}
    (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hp : p∈Icc (19/50:ℝ) lam) (hz : z∈Icc (7/8:ℝ) 1)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hN : 0<denominator lam S p t) (hJ : 0<betaNumerator lam p t)
    (hD : 0≤etaNumerator lam S p t) (hs : 0<1+Certificates.SmallMassExpressions.slope lam S)
    (hY : 8793/100000≤Y) (hH : H∈Icc (-(3589/10000):ℝ) (-(1757/5000)))
    (hscore : phi z=tailScore (539/625) Y H z)
    (hprimitive : curvePrimitive phi z=tailPrimitive (539/625) Y H z)
    (hnlo : ExtendedTailPolynomialSigns lam S p t (-(3589/10000)))
    (hnhi : ExtendedTailPolynomialSigns lam S p t (-(1757/5000))) :
    ∀ q∈Icc (0:ℝ) p,z+q-lam+
      extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*packingK phi p q z+
      extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
  have hR := g.line_primitive p ⟨by linarith only [hp.1],by linarith only [hp.2,g.lambda_mem.2]⟩
  have hP := g.line_primitive (1-p) ⟨by linarith only [hp.2,g.lambda_mem.2],by linarith only [hp.1]⟩
  intro q hq
  have hlo := fixed_anchor_tail_envelope_nonpos h g hp hz hinitial hcapOrder hJ hs hnlo q hq
  have hhi := fixed_anchor_tail_envelope_nonpos h g hp hz hinitial hcapOrder hJ hs hnhi q hq
  let C := denominator lam S p t*(z+q-lam)+betaNumerator lam p t*
    (curvePrimitive phi (z-p+q)-curvePrimitive phi q)
  have hl : C+etaNumerator lam S p t*tailScore (539/625) (8793/100000) (-(3589/10000)) z-
      betaNumerator lam p t*tailPrimitive (539/625) (8793/100000) (-(3589/10000)) z≤0 := by
    convert! hlo using 1 <;> dsimp [C,extendedTailEnvelope] <;> ring
  have hh : C+etaNumerator lam S p t*tailScore (539/625) (8793/100000) (-(1757/5000)) z-
      betaNumerator lam p t*tailPrimitive (539/625) (8793/100000) (-(1757/5000)) z≤0 := by
    convert! hhi using 1 <;> dsimp [C,extendedTailEnvelope] <;> ring
  have hactual := weighted_tail_nonpos_of_anchor_endpoints (by norm_num : (539/625:ℝ)<1)
    (show z∈Icc (539/625:ℝ) 1 from ⟨by linarith only [hz.1],hz.2⟩) hY hH hJ.le hD hl hh
  have he : extendedTailEnvelope phi lam S p t z Y H q≤0 := by
    convert! hactual using 1 <;> dsimp [C,extendedTailEnvelope] <;> ring
  rw [hR,hP,beta_eq,eta_eq]
  apply nonpos_of_mul_nonpos_left (b:=denominator lam S p t) _ hN
  unfold packingK
  rw [hscore,hprimitive]
  convert! he using 1 <;> unfold extendedTailEnvelope <;> field_simp [hN.ne'] <;> ring

end OptimalG
