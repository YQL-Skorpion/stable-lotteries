import OptimalG.SmallMassCapSupport
import OptimalG.SmallMassDefectEndpoints
import OptimalG.SmallMassCoefficients
import OptimalG.VerifierAssembly

/-! Complete C.4 verifier test on [.04,.14]. Its numerical premises are
scalar rational/minimum expressions; all split and rank extensions are proved. -/
namespace OptimalG
open Set

noncomputable def intermediateSmallEta (phi : ℝ→ℝ) (lam S p : ℝ) : ℝ :=
  smallMassCapEta phi lam p (smallMassBeta (curvePrimitive phi) lam S p)
    (smallMassTarget (curvePrimitive phi) lam S p)

structure IntermediateSmallMassChecks (phi : ℝ→ℝ) (lam S p : ℝ) : Prop where
  beta_mass : smallMassBeta (curvePrimitive phi) lam S p*p≤1
  target : lam≤smallMassTarget (curvePrimitive phi) lam S p
  head_zero : intermediateSmallEta phi lam S p*phi 0≤smallMassTarget (curvePrimitive phi) lam S p
  split_margin : 1≤smallMassBeta (curvePrimitive phi) lam S p*(phi 0-lam+391/500-p)
  defect_coefficient : smallMassBeta (curvePrimitive phi) lam S p*(1-391/500)/2-
    intermediateSmallEta phi lam S p≤0
  endpoint_switch : smallMassDefectProxy lam p (smallMassBeta (curvePrimitive phi) lam S p)
    (intermediateSmallEta phi lam S p) (391/500) (789/1000) (13/50) (789/1000)≤0
  endpoint_one : smallMassDefectProxy lam p (smallMassBeta (curvePrimitive phi) lam S p)
    (intermediateSmallEta phi lam S p) (391/500) (789/1000) (13/50) 1≤0

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem intermediateSmallMass_test {S p slope : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hp : p∈Icc (1/25:ℝ) (7/50)) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hhead : ∀ x∈Icc (0:ℝ) (527/2000),phi x=phi 0+slope*x)
    (hcap : ∀ x∈Icc (527/2000:ℝ) (7/25),phi x=Variational.capScore lam S x)
    (hline : ∀ z∈Icc lam (391/500),phi z=lam-z)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hstart : curvePrimitive phi (391/500)=Variational.quadratic lam (391/500)-S)
    (hprimitive : ∀ r∈Icc (19/50:ℝ) 1,curvePrimitive phi r≤Variational.quadratic lam r-S)
    (hdefect : ∀ z∈Icc (391/500:ℝ) 1,(13/50)*max (z-789/1000) 0≤scoreDefect phi lam z)
    (hn : IntermediateSmallMassChecks phi lam S p) :
    ThreeFunctionTest phi lam p (smallMassBeta (curvePrimitive phi) lam S p)
      (intermediateSmallEta phi lam S p) := by
  let beta := smallMassBeta (curvePrimitive phi) lam S p
  let target := smallMassTarget (curvePrimitive phi) lam S p
  let eta := intermediateSmallEta phi lam S p
  have hp0 : 0<p := by linarith only [hp.1]
  have hp1 : p<1 := by linarith only [hp.2]
  have hpl : p≤lam := by linarith only [hp.2,hlam.1]
  have hP := hprimitive (1-p) ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  have hPpos := h.primitive_pos (q:=1-p)
    ⟨by linarith only [hp1],by linarith only [hp0]⟩
  have hD : 0<smallMassDenominator (curvePrimitive phi) lam S p := by
    have hR := h.primitive_pos ⟨hp0,hp1⟩
    dsimp [smallMassDenominator]
    linarith only [hR,hP,hPpos]
  have hb : 0≤beta := (div_pos (by linarith only [hlam.1,hp0]) hD).le
  have hs := h.smallMass_cap_support hlam hS ⟨mul_nonneg hb hp0.le,hn.beta_mass⟩
    hn.target hhead hcap hn.head_zero
  change 1≤eta ∧ eta≤1+beta*p ∧ ∀ x∈Icc 0 lam,x+eta*phi x≤target at hs
  have hsupport2 : ∀ x∈Icc 0 lam,x+eta*phi x≤lam-p+beta*curvePrimitive phi p := hs.2.2
  have hsupport1 : ∀ x∈Icc 0 lam,x+eta*phi x≤2*lam-beta*curvePrimitive phi (1-p) := by
    have hid : target=2*lam-beta*(Variational.quadratic lam (1-p)-S) :=
      smallMassTarget_identity (ne_of_gt hD)
    have hm := mul_le_mul_of_nonneg_left hP hb
    intro x hx
    have hh := hs.2.2 x hx
    rw [hid] at hh
    linarith only [hh,hm]
  have hlow (u : ℝ) (hu : u∈Icc 0 lam) : phi 0-u≤phi u := by
    have hh := hfall 0 u le_rfl hu.1 (by linarith only [hu.2,hlam.2])
    linarith only [hh]
  have hstartProxy : smallMassDefectProxy lam p beta eta (391/500) (789/1000) (13/50) (391/500)≤0 := by
    have he : 0≤1+beta*p-eta := by linarith only [hs.2.1]
    have hh := hn.endpoint_switch
    change smallMassDefectProxy lam p beta eta (391/500) (789/1000) (13/50) (789/1000)≤0 at hh
    norm_num [smallMassDefectProxy] at hh ⊢
    nlinarith only [he,hh]
  apply threeFunctionTest_of_supports h hp0 hpl
    (z0:=391/500) (by linarith only [hlam.2]) (by norm_num)
    hb (by linarith only [hs.1]) hs.2.1 hlow hline hfall
    hn.split_margin hsupport1
    (fun y hy => hsupport2 y ⟨hp0.le.trans hy.1,hy.2⟩)
  exact h.smallMass_third_of_defect_endpoints hc (by linarith only [hlam.2])
    (by norm_num) (by norm_num) hb (by norm_num) hstart
    (hline (391/500) ⟨by linarith only [hlam.2],le_rfl⟩)
    (fun z hz => hprimitive (z-p) ⟨by linarith only [hz.1,hp.2],by linarith only [hz.2,hp.1]⟩)
    hdefect hn.defect_coefficient hstartProxy hn.endpoint_switch hn.endpoint_one

end VerifierCurve
end OptimalG
