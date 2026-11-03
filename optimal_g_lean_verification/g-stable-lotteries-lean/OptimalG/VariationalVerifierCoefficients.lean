import OptimalG.SupportingCoefficients
import OptimalG.VariationalHighShape
import OptimalG.PrimitiveBounds

/-! Balanced C.4 coefficients are actual controls of the variational ODE.
Existence follows from compact supporting maxima, rather than a chosen
numerical approximation to their maximizing ranks. -/
namespace OptimalG.Variational
open Set

/-- At a mass below both maximizing ranks, the two supporting maxima coincide.
The variational coefficient then is exactly the C.21 transport coefficient. -/
theorem balanced_beta_of_common_supports {phi : ℝ→ℝ} {lam p R P eta beta x y : ℝ}
    (hD : R+P≠0)
    (hx : x+eta*phi x=2*lam-beta*P)
    (hy : y+eta*phi y=lam-p+beta*R)
    (hxSecond : x+eta*phi x≤lam-p+beta*R)
    (hyFirst : y+eta*phi y≤2*lam-beta*P) :
    beta=(lam+p)/(R+P) ∧
    2*lam-beta*P=lam-p+beta*R := by
  have he : 2*lam-beta*P=lam-p+beta*R := by
    apply le_antisymm <;> linarith only [hx,hy,hxSecond,hyFirst]
  refine ⟨(eq_div_iff hD).mpr ?_,he⟩
  nlinarith only [he]

theorem balanced_feature_coefficients {lam p x y eta beta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : (p,x,y)∈controlDomain)
    {A B : ℝ}
    (hx : eta*A=2*lam-x-beta*(quadratic lam (1-p)-d.S))
    (hy : eta*B=lam-p-y+beta*primitive lam d p) :
    eta*featureTheta lam d ((p,x,y),A,B)=1 ∧
    eta*featureAlpha lam d ((p,x,y),A,B)=beta := by
  have hD : controlDeterminant lam d (p,x,y)≠0 := by
    have hh := hd.determinant_positive hc
    linarith only [hh]
  have htheta : eta*(primitive lam d p*A+(quadratic lam (1-p)-d.S)*B)=
      controlDeterminant lam d (p,x,y) := by
    dsimp [controlDeterminant,Certificates.Control.det]
    nlinarith only [congrArg (fun t => primitive lam d p*t) hx,
      congrArg (fun t => (quadratic lam (1-p)-d.S)*t) hy]
  have halpha : eta*((p+y-lam)*A+(2*lam-x)*B)=
      beta*controlDeterminant lam d (p,x,y) := by
    dsimp [controlDeterminant,Certificates.Control.det]
    nlinarith only [congrArg (fun t => (p+y-lam)*t) hx,
      congrArg (fun t => (2*lam-x)*t) hy]
  constructor
  · change eta*((primitive lam d p*A+(quadratic lam (1-p)-d.S)*B)/
      controlDeterminant lam d (p,x,y))=1
    rw [←mul_div_assoc,htheta,div_self hD]
  · change eta*(((p+y-lam)*A+(2*lam-x)*B)/controlDeterminant lam d (p,x,y))=beta
    rw [←mul_div_assoc,halpha,mul_div_cancel_right₀ _ hD]

theorem verifier_coefficients_exist {phi : ℝ→ℝ} {lam p : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hphi : VerifierCurve phi lam)
    (hp : p∈Icc (527/2000:ℝ) pHi)
    (hgraph : ∀ x∈Icc xLo xHi,(x,phi x)∈rankScoreSupport d.phi)
    (hJ : curvePrimitive phi p=primitive lam d p)
    (hP : curvePrimitive phi (1-p)=quadratic lam (1-p)-d.S) :
    ∃ eta beta x y : ℝ, 0<eta ∧ 0<beta ∧ x∈Icc xLo xHi ∧
      y∈Icc (max xLo p) xHi ∧
      eta*phi x=2*lam-x-beta*curvePrimitive phi (1-p) ∧
      eta*phi y=lam-p-y+beta*curvePrimitive phi p ∧
      (∀ t∈Icc xLo xHi,t+eta*phi t≤2*lam-beta*curvePrimitive phi (1-p)) ∧
      (∀ t∈Icc (max xLo p) xHi,t+eta*phi t≤lam-p+beta*curvePrimitive phi p) ∧
      ((p,x,y),phi x,phi y)∈controlFeatureSupport d ∧
      eta*featureTheta lam d ((p,x,y),phi x,phi y)=1 ∧
      eta*featureAlpha lam d ((p,x,y),phi x,phi y)=beta := by
  have hp' : p∈Icc pLo pHi := ⟨by norm_num [pLo] at *; linarith only [hp.1],hp.2⟩
  have hp0 : 0<p := by linarith only [hp.1]
  have hpx : p≤xHi := by have hh := hp.2; norm_num [pHi,xHi] at *; linarith
  have hxl : xHi<lam := by have hh := hd.1.1; norm_num [lambdaLo,xHi] at *; linarith
  have hx0 : 0≤xLo := by norm_num [xLo]
  have hxx : xLo≤xHi := by norm_num [xLo,xHi]
  have hK : (Icc xLo xHi).Nonempty := ⟨xLo,le_rfl,hxx⟩
  have hL : (Icc (max xLo p) xHi).Nonempty := ⟨xHi,max_le hxx hpx,le_rfl⟩
  have hcK := hphi.continuous.mono (Icc_subset_Icc hx0 (hxl.le.trans hphi.lam_lt_one.le))
  have hcL : ContinuousOn phi (Icc (max xLo p) xHi) :=
    hcK.mono (Icc_subset_Icc (le_max_left xLo p) le_rfl)
  have hposK (x : ℝ) (hx : x∈Icc xLo xHi) : 0<phi x :=
    hphi.positive ⟨hx0.trans hx.1,hx.2.trans_lt hxl⟩
  have hposL (y : ℝ) (hy : y∈Icc (max xLo p) xHi) : 0<phi y :=
    hposK y ⟨(le_max_left _ _).trans hy.1,hy.2⟩
  have hcontrol (x y : ℝ) (hx : x∈Icc xLo xHi) (hy : y∈Icc (max xLo p) xHi) :
      (p,x,y)∈controlDomain := by
    exact ⟨hp',hx,by simpa only [max_comm] using hy⟩
  have hdet (x : ℝ) (hx : x∈Icc xLo xHi) (y : ℝ) (hy : y∈Icc (max xLo p) xHi) :
      0<determinant lam p x y (curvePrimitive phi p) (curvePrimitive phi (1-p)) := by
    rw [hJ,hP]
    change 0<controlDeterminant lam d (p,x,y)
    linarith only [hd.determinant_positive (hcontrol x y hx hy)]
  have hR := hphi.primitive_pos ⟨hp0,hpx.trans_lt (hxl.trans hphi.lam_lt_one)⟩
  have hPP := hphi.primitive_pos (q:=1-p)
    ⟨by linarith only [hpx,hxl,hphi.lam_lt_one],by linarith only [hp0]⟩
  have hyhigh : ∃ y∈Icc (max xLo p) xHi,lam-p≤y := by
    refine ⟨xHi,⟨max_le hxx hpx,le_rfl⟩,?_⟩
    have hh := hd.1.2
    norm_num [lambdaHi,xHi] at hh ⊢
    linarith only [hh,hp.1]
  obtain ⟨eta,beta,x,y,heta,hbeta,hx,hy,hxeq,hyeq,hsx,hsy⟩ :=
    supporting_coefficients_exist phi (Icc xLo xHi) (Icc (max xLo p) xHi)
      isCompact_Icc isCompact_Icc hK hL hcK hcL hposK hposL
      lam p (curvePrimitive phi p) (curvePrimitive phi (1-p)) hR hPP hdet hyhigh
  have hv := hd.feature_mem_support_of_rankScores hp' (hgraph x hx)
    (hgraph y ⟨(le_max_left _ _).trans hy.1,hy.2⟩) ((le_max_right _ _).trans hy.1)
  have he := balanced_feature_coefficients hd (hcontrol x y hx hy)
    (by simpa only [hP] using hxeq) (by simpa only [hJ] using hyeq)
  exact ⟨eta,beta,x,y,heta,hbeta,hx,hy,hxeq,hyeq,hsx,hsy,hv,he⟩

/-- The supporting coefficients convert the actual ODE bound into the zero-split
third verifier inequality wherever the shifted primitive lies on Q−S. -/
theorem balanced_control_third {phi : ℝ→ℝ} {lam p x y eta beta z : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (heta : 0≤eta)
    (hv : ((p,x,y),phi x,phi y)∈controlFeatureSupport d)
    (hcoeff : eta*featureTheta lam d ((p,x,y),phi x,phi y)=1 ∧
      eta*featureAlpha lam d ((p,x,y),phi x,phi y)=beta)
    (hscore : phi z≤featureH hd z (curvePrimitive phi z) ((p,x,y),phi x,phi y))
    (hshift : curvePrimitive phi (z-p)=quadratic lam (z-p)-d.S) :
    z-lam+beta*packingK phi p 0 z+eta*phi z≤0 := by
  rw [featureH_as_highAffineControl hd hv (curvePrimitive phi) z] at hscore
  have hh := mul_le_mul_of_nonneg_left hscore heta
  dsimp [highAffineControl] at hh
  have he : eta*(-featureTheta lam d ((p,x,y),phi x,phi y)*(z-lam)-
      featureAlpha lam d ((p,x,y),phi x,phi y)*(quadratic lam (z-p)-d.S-curvePrimitive phi z))=
      -(z-lam)-beta*(quadratic lam (z-p)-d.S-curvePrimitive phi z) := by
    nlinarith only [congrArg (fun t => t*(z-lam)) hcoeff.1,
      congrArg (fun t => t*(quadratic lam (z-p)-d.S-curvePrimitive phi z)) hcoeff.2]
  rw [he] at hh
  simp only [packingK,add_zero,curvePrimitive,intervalIntegral.integral_same,sub_zero]
  change z-lam+beta*(curvePrimitive phi (z-p)-curvePrimitive phi z)+eta*phi z≤0
  rw [hshift]
  linarith only [hh]

end OptimalG.Variational
