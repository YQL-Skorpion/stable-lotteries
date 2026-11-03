import OptimalG.CompletedBaseSupport
import OptimalG.VariationalInitialSlack
import OptimalG.VariationalMassTest
import OptimalG.IntermediateMixedCoverage
import OptimalG.Certificates.VariationalSplitGap

/-! The actual completed minimizer supplies the variational mass range.
Balanced supports exist by compactness; their coefficient bounds and split
margin are derived here rather than left as additional verifier hypotheses. -/
namespace OptimalG.Variational
open Set

theorem completed_curve_variational_mass {phi : ℝ → ℝ} {lam slope c p : ℝ}
    {d : LowRankData} (hd : Admissible lam d) (h : VerifierCurve phi lam)
    (g : BinaryCurveGeometry phi lam d.S slope c)
    (hS : d.S ∈ Icc (227179/10000000 : ℝ) (11677/500000))
    (hp : p ∈ Icc (527/2000 : ℝ) (9/25))
    (hinitial : phi 0 = Certificates.SmallMassExpressions.initial lam d.S)
    (hline : ∀ r ∈ Icc (9/25 : ℝ) (391/500), phi r=lam-r)
    (hgraph : ∀ r ∈ Icc xLo xHi, (r,phi r) ∈ rankScoreSupport d.phi)
    (hprimitive : ∀ r ∈ Icc (527/2000 : ℝ) xHi,
      curvePrimitive phi r = primitive lam d r)
    (hcontrol : ∀ r ∈ Icc zStart 1, ∀ v ∈ controlFeatureSupport d,
      phi r ≤ featureH hd r (curvePrimitive phi r) v) :
    ∃ beta eta, ThreeFunctionTest phi lam p beta eta := by
  have hL : lam ∈ Icc (22493/40000 : ℝ) (56233/100000) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hJ := hprimitive p ⟨hp.1,hp.2.trans (by norm_num [xHi])⟩
  have hP := g.line_primitive (1-p)
    ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  obtain ⟨eta,beta,x,y,heta,hbeta,hx,hy,hxeq,hyeq,hsx,hsy,hv,hcoeff⟩ :=
    verifier_coefficients_exist hd h
      ⟨hp.1,by norm_num [pHi] at *; exact hp.2⟩ hgraph hJ hP
  have hcap := g.cap_score (1459/5000) ⟨by norm_num,g.contact_mem.1⟩
  have hband : (1459/5000 : ℝ) ≤ p → lam-p-11/500 ≤ phi p := by
    intro hpCap
    have hs := hd.capSlack_lt_initial_band (by linarith only [hS.2])
      (c:=1459/5000) ⟨by norm_num,by norm_num [xHi]⟩
    have hf := g.low_slope (1459/5000) p (by norm_num) hpCap
      (by linarith only [hp.2,hL.1])
    rw [hcap] at hf
    unfold capSlack at hs
    linarith only [hs,hf]
  have hsx' : ∀ r ∈ Icc (57/200 : ℝ) (19/50),
      r+eta*phi r ≤ 2*lam-beta*curvePrimitive phi (1-p) := by
    convert hsx using 1 <;> norm_num [xLo,xHi]
  have hsy' : ∀ r ∈ Icc (max (57/200) p : ℝ) (19/50),
      r+eta*phi r ≤ lam-p+beta*curvePrimitive phi p := by
    convert hsy using 1 <;> norm_num [xLo,xHi]
  have he := balanced_eta_bounds hd (by linarith only [hS.2]) hp heta
    hJ hP hcap hband hsx' hsy' hv hcoeff.1
  have hgap := Certificates.variational_split_gap h hL hS hp hbeta.le he.1.le
    hinitial (hline (9/25) ⟨le_rfl,by norm_num⟩)
    (g.cap_upper p ⟨by linarith only [hp.1],by linarith only [hp.2]⟩)
    (hsy' (9/25) ⟨max_le (by norm_num) hp.2,by norm_num⟩)
  have hzero : phi 0 ≤ 443/1000 := by
    rw [hinitial]
    exact (Certificates.SmallMassExpressions.initial_bounds hL hS).2
  refine ⟨beta,eta,?_⟩
  apply h.variational_mass_test hd
    ⟨by linarith only [hL.1],by linarith only [hL.2]⟩
    ⟨by linarith only [hS.1],by linarith only [hS.2]⟩ hp hbeta.le
    ⟨by linarith only [he.1],he.2.le⟩ hzero (by linarith only [g.head_slope]) g.head
    (fun r hr => g.cap_score r ⟨hr.1,by linarith only [hr.2,g.contact_mem.1]⟩)
    (fun r hr => hline r ⟨by linarith only [hr.1],hr.2⟩)
    (g.fall_through_line (fun r hr => hline r
      ⟨by linarith only [hr.1,hL.1],hr.2⟩))
    (g.line_primitive (19/50) ⟨by norm_num,by norm_num⟩)
    hsx' hsy' hv hcoeff
    (fun z hz => hcontrol z ⟨by norm_num [zStart]; linarith only [hz.1],hz.2⟩ _ hv)
    hgap.le

end OptimalG.Variational
