import OptimalG.CompletedSmallMassGeometry
import OptimalG.VariationalBalancedBounds
import OptimalG.VariationalVerifierCoefficients
import OptimalG.VariationalSupportExtension
import OptimalG.TransportSmallMass

/-! The transport endpoint at mass .2635 is an actual balanced variational
control. Equality of the two support domains fixes its beta, and the supporting
infimum only improves its high-rank test. -/
namespace OptimalG.Variational
open Set

theorem completed_transport_endpoint {phi : ℝ→ℝ} {lam slope c : ℝ}
    {d : LowRankData} (hd : Admissible lam d) (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam d.S slope c)
    (hS : d.S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hgraph : ∀ r∈Icc xLo xHi,(r,phi r)∈rankScoreSupport d.phi)
    (hprimitive : ∀ r∈Icc (527/2000:ℝ) xHi,
      curvePrimitive phi r=primitive lam d r)
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport d,
      phi r≤featureH hd r (curvePrimitive phi r) v)
    (htarget : lam<smallMassTarget (curvePrimitive phi) lam d.S (527/2000)) :
    ∀ z∈Icc (391/500:ℝ) 1,
      smallMassPsi (curvePrimitive phi) phi
        (smallMassBeta (curvePrimitive phi) lam d.S)
        (smallMassTarget (curvePrimitive phi) lam d.S) lam (527/2000) z≤0 := by
  have hJ := hprimitive (527/2000) ⟨le_rfl,by norm_num [xHi]⟩
  have hP := g.line_primitive (1-527/2000) ⟨by norm_num,by norm_num⟩
  obtain ⟨eta,beta,x,y,heta,hbeta,hx,hy,hxeq,hyeq,hsx,hsy,hv,hcoeff⟩ :=
    verifier_coefficients_exist hd h (p:=527/2000)
      ⟨le_rfl,by norm_num [pHi]⟩ hgraph hJ hP
  have hsx' : ∀ r∈Icc (57/200:ℝ) (19/50),
      r+eta*phi r≤2*lam-beta*curvePrimitive phi (1-527/2000) := by
    convert hsx using 1 <;> norm_num [xLo,xHi]
  have hsy' : ∀ r∈Icc (max (57/200) (527/2000):ℝ) (19/50),
      r+eta*phi r≤lam-527/2000+beta*curvePrimitive phi (527/2000) := by
    convert hsy using 1 <;> norm_num [xLo,xHi]
  have he := balanced_eta_bounds hd (by linarith only [hS.2])
    (p:=527/2000) ⟨le_rfl,by norm_num⟩ heta hJ hP
    (g.cap_score (1459/5000) ⟨by norm_num,g.contact_mem.1⟩)
    (by intro hp; norm_num at hp) hsx' hsy' hv hcoeff.1
  have hD : curvePrimitive phi (527/2000)+curvePrimitive phi (1-527/2000)≠0 :=
    ne_of_gt (add_pos (h.primitive_pos (by constructor <;> norm_num))
      (h.primitive_pos (by constructor <;> norm_num)))
  have hx' : x∈Icc (max xLo (527/2000)) xHi := by
    refine ⟨max_le hx.1 ?_,hx.2⟩
    have hh := hx.1
    norm_num [xLo] at hh
    linarith only [hh]
  have hy' : y∈Icc xLo xHi := ⟨(le_max_left _ _).trans hy.1,hy.2⟩
  have hb := (balanced_beta_of_common_supports hD (by linarith only [hxeq]) (by linarith only [hyeq])
    (hsy x hx') (hsx y hy')).1
  have hb' : beta=smallMassBeta (curvePrimitive phi) lam d.S (527/2000) := by
    rw [hb,hP]
    simp only [smallMassBeta,smallMassDenominator,add_sub_assoc]
  have hlocal := h.local_support_to_global
    (show lam∈Icc (1/2:ℝ) (57/100) by
      constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2])
    (show d.S∈Icc (0:ℝ) (3/100) by constructor <;> linarith only [hS.1,hS.2])
    ⟨by linarith only [he.1],he.2.le⟩ (by linarith only [g.head_slope])
    (p:=0) (by constructor <;> norm_num) g.head
    (fun r hr => g.cap_score r ⟨hr.1,by linarith only [hr.2,g.contact_mem.1]⟩)
    (g.line_score (19/50) ⟨by norm_num,by norm_num⟩)
    (fun r hr => hsx' r ⟨(le_max_left _ _).trans hr.1,hr.2⟩)
  have hden : smallMassDenominator (curvePrimitive phi) lam d.S (527/2000)≠0 := by
    unfold smallMassDenominator
    rw [add_sub_assoc,←hP]
    exact hD
  have hs : ∀ r∈Icc (0:ℝ) lam,
      r+eta*phi r≤smallMassTarget (curvePrimitive phi) lam d.S (527/2000) := by
    intro r hr
    have hh := hlocal r hr
    rw [hb',hP,←smallMassTarget_identity hden] at hh
    exact hh
  intro z hz
  apply h.smallMass_endpoint_of_stored htarget
    ⟨by linarith only [g.lambda_mem.2,hz.1],hz.2⟩ hs
  rw [←hb']
  exact balanced_control_third hd heta.le hv hcoeff
    (hcontrol z ⟨by norm_num [zStart]; linarith only [hz.1],hz.2⟩ _ hv)
    (g.line_primitive (z-527/2000)
      ⟨by linarith only [hz.1],by linarith only [hz.2]⟩)

end OptimalG.Variational
