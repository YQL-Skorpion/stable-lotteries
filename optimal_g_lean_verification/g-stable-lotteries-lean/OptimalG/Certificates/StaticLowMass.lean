import OptimalG.CompletedTransportEndpoint
import OptimalG.IntermediateMixedCoverage
import OptimalG.IntermediateSmallMassControl
import OptimalG.Certificates.StaticCurveMassFacts
import OptimalG.Certificates.StaticSmallMassDirectCertificate
import OptimalG.Certificates.StaticSmallMassHeadCertificate
import OptimalG.Certificates.StaticSmallMassMinimizerCertificate

/-! Actual low-mass assembly through .2635. The direct test uses a supported
cap control. Both transport intervals start from proved high-rank tests, with
the rightmost endpoint obtained from the actual balanced variational control. -/
namespace OptimalG.Variational
open Set
open Certificates.SmallMassExpressions

variable {phi : ℝ→ℝ} {slope c : ℝ}

 theorem static_curve_direct_mass (hd : Admissible (Certificates.StaticLow.lam:ℝ) staticLowData)
    (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ)) (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) staticLowData.S slope c)
    (hS : staticLowData.S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc (Certificates.StaticLow.lam:ℝ) 1) phi)
    (hinitial : phi 0=initial (Certificates.StaticLow.lam:ℝ) staticLowData.S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=(Certificates.StaticLow.lam:ℝ)-r)
    (hgraph : ∀ r∈Icc xLo xHi,(r,phi r)∈rankScoreSupport staticLowData.phi)
    (hprimitive : ∀ r∈Icc (527/2000:ℝ) xHi,
      curvePrimitive phi r=primitive (Certificates.StaticLow.lam:ℝ) staticLowData r)
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      phi r≤featureH hd r (curvePrimitive phi r) v) :
    ∀ p∈Icc (1/25:ℝ) (7/50),∃ beta eta,ThreeFunctionTest phi (Certificates.StaticLow.lam:ℝ) p beta eta := by
  have hL : (Certificates.StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hhead := g.standard_head hinitial
  have hfixed := completed_curve_fixed_cap_control hd g hgraph hprimitive hcontrol
  have hm := Certificates.StaticMass.fixed_cap_margins
  have hcap : ∀ r∈Icc (527/2000:ℝ) (7/25),phi r=capScore (Certificates.StaticLow.lam:ℝ) staticLowData.S r :=
    fun r hr => g.cap_score r ⟨hr.1,by linarith only [hr.2,g.contact_mem.1]⟩
  intro p hp
  refine ⟨_,_,h.intermediateSmallMass_test_of_control
    (show (Certificates.StaticLow.lam:ℝ)∈Icc (1/2:ℝ) (57/100) by constructor <;> linarith only [hL.1,hL.2])
    (show staticLowData.S∈Icc (0:ℝ) (3/100) by constructor <;> linarith only [hS.1,hS.2])
    hp hc g.head hcap ?_ ?_ ?_ hm.1.le hm.2.1.le hm.2.2.le hfixed ?_⟩
  · intro z hz
    exact hline z ⟨by linarith only [hz.1],hz.2⟩
  · exact g.fall_through_line (fun r hr => hline r
      ⟨by linarith only [hr.1,hL.1],hr.2⟩)
  · exact g.line_primitive (19/50) ⟨by norm_num,by norm_num⟩
  · exact static_intermediate_checks h hL hS hp hhead (hcap (7/25) ⟨by norm_num,le_rfl⟩)

 theorem static_curve_transport_mass (hd : Admissible (Certificates.StaticLow.lam:ℝ) staticLowData)
    (h : VerifierCurve phi (Certificates.StaticLow.lam:ℝ)) (g : BinaryCurveGeometry phi (Certificates.StaticLow.lam:ℝ) staticLowData.S slope c)
    (hS : staticLowData.S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc (Certificates.StaticLow.lam:ℝ) 1) phi)
    (hinitial : phi 0=initial (Certificates.StaticLow.lam:ℝ) staticLowData.S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=(Certificates.StaticLow.lam:ℝ)-r)
    (hgraph : ∀ r∈Icc xLo xHi,(r,phi r)∈rankScoreSupport staticLowData.phi)
    (hprimitive : ∀ r∈Icc (527/2000:ℝ) xHi,
      curvePrimitive phi r=primitive (Certificates.StaticLow.lam:ℝ) staticLowData r)
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      phi r≤featureH hd r (curvePrimitive phi r) v) :
    ∀ p∈Icc (7/50:ℝ) (527/2000),∃ beta eta,ThreeFunctionTest phi (Certificates.StaticLow.lam:ℝ) p beta eta := by
  have hL : (Certificates.StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hL' : (Certificates.StaticLow.lam:ℝ)∈Icc (1/2:ℝ) (57/100) :=
    ⟨by linarith only [hL.1],by linarith only [hL.2]⟩
  have hhead := g.standard_head hinitial
  have hw : phi (1459/5000)=cap2918 (Certificates.StaticLow.lam:ℝ) staticLowData.S :=
    g.cap_score (1459/5000) ⟨by norm_num,g.contact_mem.1⟩
  have hcap : ∀ r∈Icc (527/2000:ℝ) (7/25),phi r=capScore (Certificates.StaticLow.lam:ℝ) staticLowData.S r :=
    fun r hr => g.cap_score r ⟨hr.1,by linarith only [hr.2,g.contact_mem.1]⟩
  have hline' : ∀ r∈Icc (19/50:ℝ) (391/500),phi r=(Certificates.StaticLow.lam:ℝ)-r :=
    fun r hr => hline r ⟨by linarith only [hr.1],hr.2⟩
  have hfall := g.fall_through_line (fun r hr => hline r
    ⟨by linarith only [hr.1,hL.1],hr.2⟩)
  have hanchor := g.line_primitive (19/50) ⟨by norm_num,by norm_num⟩
  have hchecks := fun p hp => static_cap_transport_checks h hL hS (p:=p) hp hhead hw
  have hend := completed_transport_endpoint hd h g hS hgraph hprimitive hcontrol
    (hchecks (527/2000) ⟨by norm_num,le_rfl⟩).target
  have hupper := h.smallMass_transport_test hL' (left:=1/5) (right:=527/2000)
    (by norm_num) (by norm_num) le_rfl (cap28_pos hL hS) hc hline' hfall hanchor
    (fun p hp x hx hmin => static_cap_minimizer_score h hL hS hp hhead g.head hcap hw hx hmin)
    hchecks hend
  have hend20 : ∀ z∈Icc (391/500:ℝ) 1,
      smallMassPsi (curvePrimitive phi) phi (smallMassBeta (curvePrimitive phi) (Certificates.StaticLow.lam:ℝ) staticLowData.S)
        (smallMassTarget (curvePrimitive phi) (Certificates.StaticLow.lam:ℝ) staticLowData.S) (Certificates.StaticLow.lam:ℝ) (1/5) z≤0 := by
    intro z hz
    have hh := (hupper (1/5) ⟨le_rfl,by norm_num⟩).third z
      ⟨by linarith only [hL.2,hz.1],hz.2⟩ 0 le_rfl (by norm_num)
    simpa only [smallMassPsi,packingK,add_zero,curvePrimitive,
      intervalIntegral.integral_same,sub_zero] using hh
  have hinitial0 : 0 < initial (Certificates.StaticLow.lam:ℝ) staticLowData.S := by
    linarith only [(initial_bounds hL hS).1]
  have hlower := h.smallMass_transport_test hL' (left:=7/50) (right:=1/5)
    (by norm_num) (by norm_num) (by norm_num) hinitial0 hc hline' hfall hanchor
    (fun _ _ x hx _ => by rw [←hinitial]; exact h.supportMinimum_minimizer_score_le_zero hx)
    (fun p hp => static_head_transport_checks h hL hS hp hhead hw) hend20
  intro p hp
  by_cases hp20 : p≤1/5
  · exact ⟨_,_,hlower p ⟨hp.1,hp20⟩⟩
  · exact ⟨_,_,hupper p ⟨(lt_of_not_ge hp20).le,hp.2⟩⟩


end OptimalG.Variational

namespace OptimalG.Certificates.StaticCurve
open Set Variational

/-- Actual sufficient tests through the head/cap mass, conditional only on the
full-layer control inequalities supplied by the static high certificate. -/
theorem low_mass
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport staticLowData,
      score r≤featureH staticLow_admissible r (curvePrimitive score r) v)
    {p : ℝ} (hp : p∈Ioc (0:ℝ) (527/2000)) :
    ∃ beta eta,ThreeFunctionTest score StaticLow.lam p beta eta := by
  by_cases ht : p≤1/25
  · exact ⟨_,_,tiny_mass ⟨hp.1,ht⟩⟩
  by_cases hm : p≤7/50
  · exact static_curve_direct_mass staticLow_admissible verifierCurve binaryGeometry
      StaticMass.parameter_ranges.2 concave initial_formula line_782
      (fun _ hr => score_graph hr) (fun _ hr => primitive_variational hr) hcontrol
      p ⟨(lt_of_not_ge ht).le,hm⟩
  · exact static_curve_transport_mass staticLow_admissible verifierCurve binaryGeometry
      StaticMass.parameter_ranges.2 concave initial_formula line_782
      (fun _ hr => score_graph hr) (fun _ hr => primitive_variational hr) hcontrol
      p ⟨(lt_of_not_ge hm).le,hp.2⟩

end OptimalG.Certificates.StaticCurve
