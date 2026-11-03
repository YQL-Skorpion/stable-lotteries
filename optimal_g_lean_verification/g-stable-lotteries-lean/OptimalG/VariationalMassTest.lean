import OptimalG.VariationalVerifierCoefficients
import OptimalG.VariationalSupportExtension
import OptimalG.VerifierPrimitiveCap
import OptimalG.VerifierAssembly

/-! The entire variational mass range in C.4. Supporting coefficients,
the actual control inequality, and bounded scalar facts imply every split. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem eta_le_one_add_beta_mass {p beta eta : ℝ}
    (hp : p∈Icc (527/2000:ℝ) lam) (hb : 0≤beta)
    (heta : eta≤1000/691) (hzero : phi 0≤443/1000)
    (hsupport : lam≤lam-p+beta*curvePrimitive phi p) : eta≤1+beta*p := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hJ := h.primitive_increment_upper (a:=0) le_rfl hp0.le
    (hp.2.trans h.lam_lt_one.le)
  simp only [curvePrimitive,intervalIntegral.integral_same,sub_zero] at hJ
  change curvePrimitive phi p≤p*phi 0 at hJ
  have hscale := mul_le_mul_of_nonneg_left hJ hb
  have hprod : 0≤p*(beta*phi 0-1) := by nlinarith only [hsupport,hscale]
  have hunit := nonneg_of_mul_nonneg_right hprod hp0
  have hbound := mul_le_mul_of_nonneg_left hzero hb
  have hbeta : (1000/443:ℝ)≤beta := by nlinarith only [hunit,hbound]
  have hmass := mul_le_mul hbeta hp.1 (by norm_num : (0:ℝ)≤527/2000) hb
  norm_num at hmass
  linarith only [hmass,heta]

theorem variational_mass_test {p eta beta x y slope : ℝ} {d : Variational.LowRankData}
    (hd : Variational.Admissible lam d)
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : d.S∈Icc (0:ℝ) (3/100))
    (hp : p∈Icc (527/2000:ℝ) (9/25)) (hb : 0≤beta)
    (heta : eta∈Icc (1:ℝ) (1000/691)) (hzero : phi 0≤443/1000)
    (hslope : -(691/1000:ℝ)≤slope)
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=phi 0+slope*r)
    (hcap : ∀ r∈Icc (527/2000:ℝ) (57/200),phi r=Variational.capScore lam d.S r)
    (hline : ∀ r∈Icc (19/50:ℝ) (391/500),phi r=lam-r)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hanchor : curvePrimitive phi (19/50)=Variational.quadratic lam (19/50)-d.S)
    (hsupport1 : ∀ r∈Icc (57/200:ℝ) (19/50),
      r+eta*phi r≤2*lam-beta*curvePrimitive phi (1-p))
    (hsupport2 : ∀ r∈Icc (max (57/200) p) (19/50),
      r+eta*phi r≤lam-p+beta*curvePrimitive phi p)
    (hv : ((p,x,y),phi x,phi y)∈Variational.controlFeatureSupport d)
    (hcoeff : eta*Variational.featureTheta lam d ((p,x,y),phi x,phi y)=1 ∧
      eta*Variational.featureAlpha lam d ((p,x,y),phi x,phi y)=beta)
    (hcontrol : ∀ z∈Icc (391/500:ℝ) 1,phi z≤
      Variational.featureH hd z (curvePrimitive phi z) ((p,x,y),phi x,phi y))
    (hgap : 1≤beta*(phi 0-lam+391/500-p)) :
    ThreeFunctionTest phi lam p beta eta := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hpl : p≤lam := by linarith only [hp.2,hlam.1]
  have hxline := hline (19/50) ⟨le_rfl,by norm_num⟩
  have hs1 := h.local_support_to_global hlam hS heta hslope
    (show (0:ℝ)∈Icc 0 (19/50) by constructor <;> norm_num)
    hhead hcap hxline (fun r hr => hsupport1 r
      ⟨(le_max_left (57/200) 0).trans hr.1,hr.2⟩)
  have hs2 := h.local_support_to_global hlam hS heta hslope
    (show p∈Icc (0:ℝ) (19/50) by constructor <;> linarith only [hp.1,hp.2])
    hhead hcap hxline hsupport2
  have hbetaR := hs2 lam ⟨hpl,le_rfl⟩
  rw [h.at_lam,mul_zero,add_zero] at hbetaR
  have hetab := h.eta_le_one_add_beta_mass ⟨hp.1,hpl⟩ hb heta.2 hzero hbetaR
  have hprimitive := h.primitive_eq_quadratic_on_line (by norm_num : (0:ℝ)≤19/50)
    (by norm_num : (19/50:ℝ)≤391/500) (by norm_num : (391/500:ℝ)≤1) hanchor hline
  apply threeFunctionTest_of_supports h hp0 hpl (by linarith only [hlam.2])
    (by norm_num) hb (by linarith only [heta.1]) hetab
    (fun u hu => by
      have hh := hfall 0 u le_rfl hu.1 (by linarith only [hu.2,hlam.2])
      linarith only [hh])
    (fun r hr => hline r ⟨by linarith only [hr.1,hlam.1],hr.2⟩)
    hfall hgap hs1 hs2
  intro z hz
  exact Variational.balanced_control_third hd (by linarith only [heta.1]) hv hcoeff
    (hcontrol z hz) (hprimitive (z-p) ⟨by linarith only [hz.1,hp.2],
      by linarith only [hz.2,hp.1]⟩)

end VerifierCurve
end OptimalG
