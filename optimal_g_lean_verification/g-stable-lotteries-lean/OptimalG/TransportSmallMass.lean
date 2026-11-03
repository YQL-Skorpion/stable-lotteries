import OptimalG.SmallMassCoefficients
import OptimalG.SmallMassMinimumBounds
import OptimalG.VerifierPrimitiveCap
import OptimalG.VerifierAssembly

/-! The C.4 derivative transport gives complete tests, with all minimizing
rank, differentiability, and split extensions separated from finite checks. -/
namespace OptimalG
open Set

theorem smallMassRate_corners_of_two {lam zminus p beta b a : ℝ}
    (hlam : 0≤lam) (hz : zminus≤1) (ha : 0≤a)
    (hv : 0≤a+b*p+beta)
    (hleft : 0≤smallMassRate lam zminus p beta b a zminus 0)
    (hright : 0≤smallMassRate lam zminus p beta b a 1 lam) :
    0≤smallMassRate lam zminus p beta b a zminus 0 ∧
    0≤smallMassRate lam zminus p beta b a zminus lam ∧
    0≤smallMassRate lam zminus p beta b a 1 0 ∧
    0≤smallMassRate lam zminus p beta b a 1 lam := by
  refine ⟨hleft,?_,?_,hright⟩
  · have hh := mul_nonneg ha hlam
    dsimp [smallMassRate] at hleft ⊢
    nlinarith only [hleft,hh]
  · have hh := mul_nonneg hv (sub_nonneg.mpr hz)
    dsimp [smallMassRate] at hleft ⊢
    nlinarith only [hleft,hh]

structure TransportSmallMassChecks (phi : ℝ→ℝ) (lam S A p : ℝ) : Prop where
  target : lam<smallMassTarget (curvePrimitive phi) lam S p
  beta_derivative : smallMassBetaDerivative (curvePrimitive phi) phi lam S p≤0
  target_derivative : smallMassTargetDerivative (curvePrimitive phi) phi lam S p≤0
  support_witness : smallMassTarget (curvePrimitive phi) lam S p-1459/5000≤
    (1+smallMassBeta (curvePrimitive phi) lam S p*p)*phi (1459/5000)
  split_margin : 1≤smallMassBeta (curvePrimitive phi) lam S p*(phi 0-lam+391/500-p)
  rate_slope : 0≤ -smallMassTargetDerivative (curvePrimitive phi) phi lam S p/A+
    smallMassBetaDerivative (curvePrimitive phi) phi lam S p*p+
    smallMassBeta (curvePrimitive phi) lam S p
  rate_left : 0≤smallMassRate lam (391/500) p
    (smallMassBeta (curvePrimitive phi) lam S p)
    (smallMassBetaDerivative (curvePrimitive phi) phi lam S p)
    (-smallMassTargetDerivative (curvePrimitive phi) phi lam S p/A) (391/500) 0
  rate_right : 0≤smallMassRate lam (391/500) p
    (smallMassBeta (curvePrimitive phi) lam S p)
    (smallMassBetaDerivative (curvePrimitive phi) phi lam S p)
    (-smallMassTargetDerivative (curvePrimitive phi) phi lam S p/A) 1 lam

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem smallMass_transport_test {S A left right : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100))
    (hlr : left≤right) (hl : 0<left) (hr : right≤527/2000)
    (hApos : 0<A) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hline : ∀ z∈Icc (19/50:ℝ) (391/500),phi z=lam-z)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hanchor : curvePrimitive phi (19/50)=Variational.quadratic lam (19/50)-S)
    (hA : ∀ p∈Icc left right,∀ x∈Ico (0:ℝ) lam,
      supportMinimum phi lam (smallMassTarget (curvePrimitive phi) lam S p)=
        (smallMassTarget (curvePrimitive phi) lam S p-x)/phi x → phi x≤A)
    (hn : ∀ p∈Icc left right,TransportSmallMassChecks phi lam S A p)
    (hend : ∀ z∈Icc (391/500:ℝ) 1,
      smallMassPsi (curvePrimitive phi) phi
        (smallMassBeta (curvePrimitive phi) lam S)
        (smallMassTarget (curvePrimitive phi) lam S) lam right z≤0) :
    ∀ p∈Icc left right,ThreeFunctionTest phi lam p
      (smallMassBeta (curvePrimitive phi) lam S p)
      (supportMinimum phi lam (smallMassTarget (curvePrimitive phi) lam S p)) := by
  have hprimitive := h.primitive_le_quadratic_after_anchor
    (show (19/50:ℝ)∈Icc 0 1 by constructor <;> norm_num) hanchor
  have hstart := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤19/50)
    (by norm_num : (19/50:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1)
    hanchor hline (391/500) ⟨by norm_num,le_rfl⟩
  have hp01 (p : ℝ) (hp : p∈Icc left right) : p∈Ioo (0:ℝ) 1 :=
    ⟨hl.trans_le hp.1,by linarith only [hp.2,hr]⟩
  have hP (p : ℝ) (hp : p∈Icc left right) :
      curvePrimitive phi (1-p)≤Variational.quadratic lam (1-p)-S :=
    hprimitive (1-p) ⟨by linarith only [hp.2,hr],by linarith only [(hp01 p hp).1]⟩
  have hD (p : ℝ) (hp : p∈Icc left right) :
      0<smallMassDenominator (curvePrimitive phi) lam S p := by
    have hR := h.primitive_pos (hp01 p hp)
    have hPP := h.primitive_pos (q:=1-p)
      ⟨by linarith only [(hp01 p hp).2],by linarith only [(hp01 p hp).1]⟩
    have hh := hP p hp
    dsimp [smallMassDenominator]
    linarith only [hR,hPP,hh]
  have hbeta (p : ℝ) (hp : p∈Icc left right) :
      0≤smallMassBeta (curvePrimitive phi) lam S p :=
    (div_pos (by linarith only [h.lam_pos,(hp01 p hp).1]) (hD p hp)).le
  have hJc : ContinuousOn (curvePrimitive phi) (Icc left right) :=
    h.primitive_continuous.mono (by intro p hp; exact ⟨(hp01 p hp).1.le,(hp01 p hp).2.le⟩)
  have hJd (p : ℝ) (hp : p∈Ioo left right) :=
    h.primitive_hasDerivAt (hp01 p ⟨hp.1.le,hp.2.le⟩)
  have hanti := smallMassTarget_antitone hJc hJd
    (fun p hp => ne_of_gt (hD p hp))
    (fun p hp => (hn p ⟨hp.1.le,hp.2.le⟩).target_derivative)
  have hbase (z : ℝ) (hz : z∈Icc (391/500:ℝ) 1) :=
    h.smallMass_third_transport hc (by linarith only [hlam.2]) hz hlr hl
      (by linarith only [hr]) hstart
      (hline (391/500) ⟨by norm_num,le_rfl⟩)
      (fun p hp => hprimitive (z-p) ⟨by linarith only [hz.1,hp.2,hr],
        by linarith only [hz.2,(hp01 p hp).1]⟩)
      (fun p hp => (hn p hp).target) hanti hA
      (smallMassBeta_continuousOn hJc (fun p hp => ne_of_gt (hD p hp)))
      (smallMassTarget_continuousOn hJc (fun p hp => ne_of_gt (hD p hp)))
      (fun p hp => smallMassBeta_hasDerivAt (hJd p hp) (ne_of_gt (hD p ⟨hp.1.le,hp.2.le⟩)))
      (fun p hp => smallMassTarget_hasDerivAt (hJd p hp) (ne_of_gt (hD p ⟨hp.1.le,hp.2.le⟩)))
      (fun p hp => hbeta p ⟨hp.1.le,hp.2.le⟩)
      (fun p hp => (hn p ⟨hp.1.le,hp.2.le⟩).beta_derivative)
      (fun p hp => smallMassRate_corners_of_two h.lam_pos.le (by norm_num)
        (div_nonneg (neg_nonneg.mpr (hn p ⟨hp.1.le,hp.2.le⟩).target_derivative) hApos.le)
        (hn p ⟨hp.1.le,hp.2.le⟩).rate_slope
        (hn p ⟨hp.1.le,hp.2.le⟩).rate_left
        (hn p ⟨hp.1.le,hp.2.le⟩).rate_right) (hend z hz)
  intro p hp
  have hn' := hn p hp
  have heta := h.supportMinimum_ge_one hn'.target
  have hetab := h.supportMinimum_le_of_witness hn'.target
    (show (1459/5000:ℝ)∈Ico 0 lam by constructor <;> linarith only [hlam.1])
    hn'.support_witness
  have hs1 (x : ℝ) (hx : x∈Icc 0 lam) :
      x+supportMinimum phi lam (smallMassTarget (curvePrimitive phi) lam S p)*phi x≤
        2*lam-smallMassBeta (curvePrimitive phi) lam S p*curvePrimitive phi (1-p) := by
    have hh := h.supportMinimum_supports hn'.target hx
    have hhP := mul_le_mul_of_nonneg_left (hP p hp) (hbeta p hp)
    have hid := smallMassTarget_identity (ne_of_gt (hD p hp))
    have hbnd : smallMassTarget (curvePrimitive phi) lam S p ≤
        2*lam-smallMassBeta (curvePrimitive phi) lam S p*curvePrimitive phi (1-p) := by
      linarith only [hid,hhP]
    exact hh.trans hbnd
  apply threeFunctionTest_of_supports h (hp01 p hp).1
    (by linarith only [hp.2,hr,hlam.1]) (by linarith only [hlam.2]) (by norm_num)
    (hbeta p hp) (by linarith only [heta]) hetab
    (fun u hu => by
      have hh := hfall 0 u le_rfl hu.1 (by linarith only [hu.2,hlam.2])
      linarith only [hh])
    (fun z hz => hline z ⟨by linarith only [hz.1,hlam.1],hz.2⟩)
    hfall hn'.split_margin hs1
    (fun y hy => h.supportMinimum_supports hn'.target ⟨(hp01 p hp).1.le.trans hy.1,hy.2⟩)
  exact fun z hz => hbase z hz p hp

end VerifierCurve
end OptimalG
