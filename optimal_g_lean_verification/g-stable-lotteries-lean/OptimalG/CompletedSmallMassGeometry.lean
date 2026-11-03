import OptimalG.BinaryCurveGeometry
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.VariationalCapControl
import OptimalG.TinyMass

/-! Elementary completed-curve inputs for the low mass ranges. These facts
use the actual head/cap joins and graph, with no verifier end test assumed. -/
namespace OptimalG
open Set
namespace Certificates.SmallMassExpressions

theorem initial_lower_436 {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    (109/250:ℝ)≤ initial lam S := by
  have ha : (8866637272/5:ℝ)≤17357832000*lam-19352000000*S-7535468817 := by
    linarith only [hL.1,hS.2]
  have hp := mul_le_mul hL.1 ha (by norm_num : (0:ℝ)≤8866637272/5)
    (by linarith only [hL.1] : 0≤lam)
  rw [initial_formula]
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2286894366)).mpr
  nlinarith only [hp]

end Certificates.SmallMassExpressions

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S slope c : ℝ}

theorem standard_head (g : BinaryCurveGeometry phi lam S slope c)
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam S) :
    ∀ r∈Icc (0:ℝ) (527/2000),
      phi r=Certificates.SmallMassExpressions.score lam S r := by
  have hj := g.head (527/2000) ⟨by norm_num,le_rfl⟩
  rw [hinitial,g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩] at hj
  have hs : slope=Certificates.SmallMassExpressions.slope lam S := by
    unfold Certificates.SmallMassExpressions.slope headSlope
    change slope=(Variational.capScore lam S (527/2000)-
      Certificates.SmallMassExpressions.initial lam S)/(527/2000)
    apply (eq_div_iff (by norm_num : (527/2000:ℝ)≠0)).mpr
    linarith only [hj]
  intro r hr
  rw [g.head r hr,hinitial,hs]
  rfl

theorem tiny_mass {lam : ℝ} {d : Variational.LowRankData}
    (h : VerifierCurve phi lam) (g : BinaryCurveGeometry phi lam d.S slope c)
    (hLhi : lam≤(562329/1000000:ℝ))
    (hS : d.S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hinitial : phi 0=Certificates.SmallMassExpressions.initial lam d.S)
    (htail : ∀ u∈Icc (24/25:ℝ) 1,
      -1+2*(1-u)≤phi u ∧ phi u≤-1+(67/10)*(1-u)) :
    ∀ p∈Ioc (0:ℝ) (1/25),∃ beta eta,ThreeFunctionTest phi lam p beta eta := by
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hzero : phi 0∈Icc (109/250:ℝ) (443/1000) := by
    rw [hinitial]
    exact ⟨Certificates.SmallMassExpressions.initial_lower_436 hL hS,
      (Certificates.SmallMassExpressions.initial_bounds hL hS).2⟩
  have hjoin : phi (527/2000)≤13/50 := by
    rw [g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩]
    have hp := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
      (by linarith only [hL.1] : 0≤lam)
    norm_num [Variational.capScore]
    nlinarith only [hp,hL.2]
  intro p hp
  refine ⟨_,_,h.tinyMass_test hp ⟨hL.1,hLhi⟩ hzero ?_ g.head hjoin htail⟩
  intro u hu
  have hh := g.low_slope 0 u le_rfl hu.1 hu.2
  linarith only [hh]

end BinaryCurveGeometry

namespace Variational

theorem completed_curve_fixed_cap_control {phi : ℝ→ℝ} {lam slope c : ℝ}
    {d : LowRankData} (hd : Admissible lam d)
    (g : BinaryCurveGeometry phi lam d.S slope c)
    (hgraph : ∀ r∈Icc xLo xHi,(r,phi r)∈rankScoreSupport d.phi)
    (hprimitive : ∀ r∈Icc (527/2000:ℝ) xHi,
      curvePrimitive phi r=primitive lam d r)
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport d,
      phi r≤featureH hd r (curvePrimitive phi r) v) :
    ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -capDiagonalTheta lam d.S (27/100) (1459/5000)*(r-lam)-
        capDiagonalAlpha lam d.S (27/100) (1459/5000)*
          (quadratic lam (r-27/100)-d.S-curvePrimitive phi r) := by
  have hc := g.cap_score (1459/5000) ⟨by norm_num,g.contact_mem.1⟩
  have hr := hgraph (1459/5000) ⟨by norm_num [xLo],by norm_num [xHi]⟩
  rw [hc] at hr
  have hR : primitive lam d (27/100)=cap lam d.S (27/100) := by
    rw [←hprimitive (27/100) ⟨by norm_num,by norm_num [xHi]⟩]
    exact g.cap_primitive (27/100) ⟨by norm_num,by linarith only [g.contact_mem.1]⟩
  have hv := hd.feature_mem_support_of_rankScores
    (show (27/100:ℝ)∈Icc pLo pHi by norm_num [pLo,pHi]) hr hr
    (by norm_num : (27/100:ℝ)≤1459/5000)
  have he := capDiagonal_coefficients (r:=1459/5000) hR
  intro r hrr
  have hh := hcontrol r ⟨by norm_num [zStart]; linarith only [hrr.1],hrr.2⟩ _ hv
  rw [featureH_as_highAffineControl hd hv (curvePrimitive phi) r] at hh
  simpa only [highAffineControl,he.1,he.2] using hh

end Variational
end OptimalG
