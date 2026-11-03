import OptimalG.VerifierAssembly
import OptimalG.TailControl

/-! Supporting inequalities and the complete three-function test for the
smallest masses. The head is affine; all remaining ranks use the score ceiling. -/
namespace OptimalG
open Set

theorem affine_score_support {phi : ℝ→ℝ} {a slope eta target : ℝ}
    (hform : ∀ x∈Icc 0 a,phi x=phi 0+slope*x)
    (hzero : eta*phi 0≤target) (hjoin : a+eta*phi a≤target) :
    ∀ x∈Icc 0 a,x+eta*phi x≤target := by
  intro x hx
  have ha : 0≤a := hx.1.trans hx.2
  have hj := hform a ⟨ha,le_rfl⟩
  have h0 : 0≤target-eta*phi 0+( -(1+eta*slope))*0+0*0^2 := by
    nlinarith only [hzero]
  have h1 : 0≤target-eta*phi 0+(-(1+eta*slope))*a+0*a^2 := by
    rw [hj] at hjoin
    nlinarith only [hjoin]
  have hh := quadratic_nonneg_between (target-eta*phi 0) (-(1+eta*slope)) 0
    0 a (by norm_num) h0 h1 x hx
  rw [hform x hx]
  nlinarith only [hh]

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem head_support_of_ceiling {a slope t ceiling : ℝ}
    (ha : a∈Icc 0 lam) (ht : 0≤t)
    (hform : ∀ x∈Icc 0 a,phi x=phi 0+slope*x)
    (hscore : phi a≤ceiling) (hzero : (1+t)*phi 0≤lam+t*ceiling) :
    ∀ x∈Icc 0 lam,x+(1+t)*phi x≤lam+t*ceiling := by
  have htail (x : ℝ) (hx : x∈Icc a lam) :
      x+(1+t)*phi x≤lam+t*ceiling := by
    have hcap := h.ceiling x ⟨ha.1.trans hx.1,hx.2.trans h.lam_lt_one.le⟩
    have hanti := h.decreasing.antitoneOn ⟨ha.1,ha.2.trans h.lam_lt_one.le⟩
      ⟨ha.1.trans hx.1,hx.2.trans h.lam_lt_one.le⟩ hx.1
    have hh := mul_le_mul_of_nonneg_left (hanti.trans hscore) ht
    nlinarith only [hcap,hh]
  have hhead := affine_score_support hform hzero (htail a ⟨le_rfl,ha.2⟩)
  intro x hx
  by_cases hxa : x≤a
  · exact hhead x ⟨hx.1,hxa⟩
  · exact htail x ⟨(lt_of_not_ge hxa).le,hx.2⟩

/-- For η=1+βp a single supporting inequality proves the first two tests;
the high-rank third test follows directly from the primitive chord estimate. -/
theorem tinyMass_threeFunctionTest {p beta target : ℝ}
    (hp : 0<p) (hpl : p≤lam) (hb : 0≤beta)
    (hlow : ∀ u∈Icc 0 lam,phi 0-u≤phi u)
    (hgap : 1≤beta*(phi 0-lam+1-p))
    (htarget1 : target≤2*lam-beta*curvePrimitive phi (1-p))
    (htarget2 : target=lam-p+beta*curvePrimitive phi p)
    (hsupport : ∀ x∈Icc 0 lam,x+(1+beta*p)*phi x≤target) :
    ThreeFunctionTest phi lam p beta (1+beta*p) := by
  have hbJ : p≤beta*curvePrimitive phi p := by
    have hh := hsupport lam ⟨h.lam_pos.le,le_rfl⟩
    rw [h.at_lam,mul_zero,add_zero,htarget2] at hh
    linarith only [hh]
  refine ⟨hb,by positivity,?_,?_,h.thirdTest_small_mass hp hpl hb hbJ⟩
  · exact h.firstTest_of_support hlow ⟨hp.le,hpl⟩ hb hgap
      (fun x hx => (hsupport x hx).trans htarget1)
  · apply secondTest_of_endpoint h hp hpl hb le_rfl
    intro y hy
    have hh := hsupport y ⟨hp.le.trans hy.1,hy.2⟩
    rw [htarget2] at hh
    linarith only [hh]

end VerifierCurve
end OptimalG
