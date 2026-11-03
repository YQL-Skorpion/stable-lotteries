import OptimalG.SupportingCrossing
import OptimalG.VariationalBalancedBounds
import OptimalG.VariationalVerifierCoefficients
import OptimalG.VariationalScoreCap
import OptimalG.BinaryCurveGeometry

/-! The base support for the extended mass range is obtained from the actual
completed score. Its parameter is the supporting line's intercept, rather than
an optimizing rank. No additional numerical certificate is required. -/
namespace OptimalG
open Set

namespace BinaryCurveGeometry

theorem score_le_cap_on_support_interval {phi : ℝ → ℝ} {lam slope c : ℝ}
    {d : Variational.LowRankData} (hd : Variational.Admissible lam d)
    (g : BinaryCurveGeometry phi lam d.S slope c) :
    ∀ r ∈ Icc (527/2000 : ℝ) Variational.xHi,
      phi r ≤ Variational.capScore lam d.S r := by
  have hjoin := g.cap_score c ⟨by linarith only [g.contact_mem.1],le_rfl⟩
  have hfree := hd.freeScore_le_capScore (theta:=691/1000)
    (by norm_num) hjoin (by
      intro r hr
      simpa only [neg_div] using g.post_slope c ⟨le_rfl,by linarith only [g.contact_mem.2]⟩ r
        ⟨hr.1,hr.2.trans (by norm_num [Variational.xHi])⟩ hr.1)
  intro r hr
  by_cases hrc : r ≤ c
  · exact (g.cap_score r ⟨hr.1,hrc⟩).le
  · exact hfree r ⟨le_of_not_ge hrc,hr.2⟩

end BinaryCurveGeometry

namespace Variational

/-- The actual graph, primitive and control inequalities of a completed
minimizer produce every base-support premise used by C.4 above mass .36. -/
theorem completed_curve_base_support {phi : ℝ → ℝ} {lam slope c : ℝ}
    {d : LowRankData} (hd : Admissible lam d) (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam d.S slope c)
    (hS : d.S ∈ Icc (227179/10000000 : ℝ) (11677/500000))
    (hgraph : ∀ r ∈ Icc xLo xHi, (r,phi r) ∈ rankScoreSupport d.phi)
    (hprimitive : ∀ r ∈ Icc (527/2000 : ℝ) xHi,
      curvePrimitive phi r = primitive lam d r)
    (hcontrol : ∀ r ∈ Icc zStart 1, ∀ v ∈ controlFeatureSupport d,
      phi r ≤ featureH hd r (curvePrimitive phi r) v) :
    ∃ t beta eta : ℝ,
      t ∈ Icc (1529/5000 : ℝ) (9/25) ∧ 0 < beta ∧
      eta ∈ Ioo (50/39 : ℝ) (1000/691) ∧
      beta*(quadratic lam (1-9/25)-d.S)+eta*(lam-t)=2*lam-t ∧
      beta*(quadratic lam (9/25)-d.S)-eta*(lam-9/25)=2*(9/25)-lam ∧
      (∀ x ∈ Icc (0 : ℝ) lam, x+eta*phi x ≤ eta*lam-(eta-1)*t) ∧
      (∀ z ∈ Icc (391/500 : ℝ) (7/8),
        z-lam+beta*packingK phi (9/25) 0 z+eta*phi z ≤ 0) := by
  have hL : lam ∈ Icc (1/2 : ℝ) (57/100) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hS' : d.S ∈ Icc (0 : ℝ) (3/100) :=
    ⟨by linarith only [hS.1],by linarith only [hS.2]⟩
  have hJ := hprimitive (9/25) ⟨by norm_num,by norm_num [xHi]⟩
  have hP := g.line_primitive (1-9/25) ⟨by norm_num,by norm_num⟩
  obtain ⟨eta,beta,x,y,heta,hbeta,hx,hy,hxeq,hyeq,hsx,hsy,hv,hcoeff⟩ :=
    verifier_coefficients_exist hd h (p:=9/25)
      ⟨by norm_num,by norm_num [pHi]⟩ hgraph hJ hP
  have hline0 := g.line_score (9/25) ⟨by norm_num,by norm_num⟩
  have hcap0 := g.cap_score (1459/5000)
    ⟨by norm_num,g.contact_mem.1⟩
  have hsx' : ∀ r ∈ Icc (57/200 : ℝ) (19/50),
      r+eta*phi r ≤ 2*lam-beta*curvePrimitive phi (1-9/25) := by
    norm_num [xLo,xHi] at hsx ⊢
    exact hsx
  have hsy' : ∀ r ∈ Icc (max (57/200) (9/25) : ℝ) (19/50),
      r+eta*phi r ≤ lam-9/25+beta*curvePrimitive phi (9/25) := by
    norm_num [xLo,xHi] at hsy ⊢
    exact hsy
  have he := balanced_eta_bounds hd (by linarith only [hS.2])
    (p:=9/25) ⟨by norm_num,le_rfl⟩ heta hJ hP hcap0
    (by intro _; rw [hline0]; linarith) hsx' hsy' hv hcoeff.1
  have he1 : 1 < eta := by linarith only [he.1]
  have he2 : eta ≤ 2 := by linarith only [he.2]
  have hlocal := h.local_support_to_global hL hS' ⟨he1.le,he.2.le⟩
    (by simpa only [neg_div] using g.head_slope) (p:=0) (by constructor <;> norm_num) g.head
    (fun r hr => g.cap_score r ⟨hr.1,by linarith only [hr.2,g.contact_mem.1]⟩)
    (g.line_score (19/50) ⟨by norm_num,by norm_num⟩)
    (fun r hr => hsx' r ⟨(le_max_left (57/200) 0).trans hr.1,hr.2⟩)
  let m := 2*lam-beta*curvePrimitive phi (1-9/25)
  let t := supportingCrossing lam m eta
  have hm : x+eta*phi x=m := by dsimp [m]; linarith only [hxeq]
  have hid : m=eta*lam-(eta-1)*t := supportingCrossing_identity (ne_of_gt he1)
  have ht : t ∈ Icc (1529/5000 : ℝ) (9/25) := by
    apply supportingCrossing_bounds h ⟨by linarith only [hL.1],hL.2⟩ hS'
      ⟨he1,he2⟩ (x:=x)
      (by constructor
          · convert hx.1 using 1 <;> norm_num [xLo]
          · have hh := hx.2; norm_num [xHi] at hh; linarith only [hh,hL.1])
      (by constructor <;> norm_num) hm
      (fun r hr => BinaryCurveGeometry.score_le_cap_on_support_interval hd g r
        ⟨by linarith only [hr.1],hr.2.trans (by norm_num [xHi])⟩)
      (cap_score_at_crossing_cut_le (by linarith only [g.lambda_mem.1]) hS.1)
    have hh := hsx' (9/25) ⟨by norm_num,by norm_num⟩
    rw [hline0] at hh
    exact hh
  have hy0 : (9/25 : ℝ) ≤ y := (le_max_right _ _).trans hy.1
  have hy1 : y ≤ 19/50 := by
    have hh := hy.2
    norm_num [xHi] at hh
    exact hh
  have hyline := g.line_score y
    ⟨by linarith only [hy0],by linarith only [hy1]⟩
  have hyupper : y+eta*phi y ≤ (9/25 : ℝ)+eta*(lam-9/25) := by
    rw [hyline]
    have hh := mul_nonneg (sub_nonneg.mpr he1.le) (sub_nonneg.mpr hy0)
    nlinarith only [hh]
  have hytest := hsy' (9/25) ⟨by norm_num,by norm_num⟩
  rw [hline0] at hytest
  have hR := g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩
  have hsecond : beta*(quadratic lam (9/25)-d.S)-eta*(lam-9/25)=2*(9/25)-lam := by
    rw [hR] at hyeq hytest
    nlinarith only [hyeq,hytest,hyupper]
  refine ⟨t,beta,eta,ht,hbeta,he,?_,hsecond,?_,?_⟩
  · dsimp only [m] at hid
    rw [hP] at hid
    nlinarith only [hid]
  · intro r hr
    exact (hlocal r hr).trans_eq hid
  · intro z hz
    exact balanced_control_third hd heta.le hv hcoeff
      (hcontrol z ⟨by norm_num [zStart]; linarith only [hz.1],by linarith only [hz.2]⟩ _ hv)
      (g.line_primitive (z-9/25)
        ⟨by linarith only [hz.1],by linarith only [hz.2]⟩)

end Variational
end OptimalG
