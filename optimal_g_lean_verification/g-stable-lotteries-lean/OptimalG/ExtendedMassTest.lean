import OptimalG.ExtendedCoefficients
import OptimalG.VerifierAssembly

/-! The final C.4 mass range. Exact coefficient identities provide both low
support tests; the remaining bounded numerical input is the high split test. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem threeFunctionTest_of_high_splits {p beta eta z0 : ℝ}
    (hp : p∈Ioc (0:ℝ) lam) (hz0 : lam≤z0) (hz1 : z0≤1)
    (hb : 0≤beta) (heta : 0≤eta) (hetab : eta≤1+beta*p)
    (hlow : ∀ u∈Icc (0:ℝ) lam,phi 0-u≤phi u)
    (hline : ∀ z∈Icc lam z0,phi z=lam-z)
    (hfall : ∀ a b,0≤a→a≤b→b≤z0→a-b≤phi b-phi a)
    (hgap : 1≤beta*(phi 0-lam+1-p))
    (hs1 : ∀ x∈Icc (0:ℝ) lam,x+eta*phi x≤2*lam-beta*curvePrimitive phi (1-p))
    (hs2 : ∀ y∈Icc p lam,y+eta*phi y≤lam-p+beta*curvePrimitive phi p)
    (hhigh : ∀ z∈Icc z0 1,∀ q,0≤q→q≤p→
      z+q-lam+beta*packingK phi p q z+eta*phi z≤0) :
    ThreeFunctionTest phi lam p beta eta := by
  have hsecond := secondTest_of_endpoint h hp.1 hp.2 hb hetab (by
    intro y hy
    linarith only [hs2 y hy])
  refine ⟨hb,heta,h.firstTest_of_support hlow ⟨hp.1.le,hp.2⟩ hb hgap hs1,hsecond,?_⟩
  intro z hz q hq hqp
  by_cases hzz : z≤z0
  · apply h.thirdTest_middle_of_endpoints hq hqp hp.2 hz0 hz1 hb hline hfall _ _ z ⟨hz.1,hzz⟩
    · have hh := hsecond lam ⟨hp.2,le_rfl⟩ q hq hqp
      linarith only [hh]
    · exact hhigh z0 ⟨le_rfl,hz1⟩ q hq hqp
  · exact hhigh z ⟨(lt_of_not_ge hzz).le,hz.2⟩ q hq hqp

theorem extended_mass_test {p t eta0 : ℝ}
    (hlam : lam∈Ioo (9/25:ℝ) (391/500)) (hp : p∈Icc (9/25:ℝ) lam)
    (ht : t∈Ico (0:ℝ) lam)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hfall : ∀ a b,0≤a→a≤b→b≤391/500→a-b≤phi b-phi a)
    (hbinary : p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p)
    (heta0 : extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))≤eta0)
    (hetab : extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))≤
      1+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*p)
    (hsupport : ∀ x∈Icc (0:ℝ) lam,x+eta0*phi x≤eta0*lam-(eta0-1)*t)
    (hgap : 1≤extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
      (phi 0-lam+1-p))
    (hhigh : ∀ z∈Icc (391/500:ℝ) 1,∀ q,0≤q→q≤p→
      z+q-lam+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
        packingK phi p q z+
        extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0) :
    ThreeFunctionTest phi lam p
      (extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p)))
      (extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))) := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hp1 : p<1 := hp.2.trans_lt h.lam_lt_one
  have hR := h.primitive_pos ⟨hp0,hp1⟩
  have hP := h.primitive_nonneg (q:=1-p)
    ⟨by linarith only [hp1],by linarith only [hp0]⟩
  have hN := extendedDenom_pos ht.2 hp.2 hR hP
  have hb := (extendedBeta_pos h.lam_pos ht hp.2 hR hP).le
  have heta := extendedEta_ge_one hN hbinary
  have hs := h.extended_supports hp.2 (ne_of_gt hN) heta heta0
    (fun y hy => hline y ⟨hp.1.trans hy.1,hy.2.trans hlam.2.le⟩) hsupport
  exact h.threeFunctionTest_of_high_splits ⟨hp0,hp.2⟩ hlam.2.le (by norm_num)
    hb (by linarith only [heta]) hetab
    (fun u hu => by
      have hh := hfall 0 u le_rfl hu.1 (hu.2.trans hlam.2.le)
      linarith only [hh])
    (fun z hz => hline z ⟨hlam.1.le.trans hz.1,hz.2⟩)
    hfall hgap hs.1 hs.2 hhigh

end VerifierCurve
end OptimalG
