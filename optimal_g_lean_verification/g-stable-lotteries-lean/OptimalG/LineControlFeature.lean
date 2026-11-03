import OptimalG.VariationalVerifierCoefficients
import OptimalG.Certificates.LineControlExpressions

/-! The fixed line control is an actual member of the essential control support.
Its coefficients use only exact line values and the scalar parameter. -/
namespace OptimalG.Variational
open Set

noncomputable def lineControlFeature (lam : ℝ) : ControlFeature :=
  ((9/25,9/25,9/25),lam-9/25,lam-9/25)

theorem lineControlFeature_mem {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hgraph : ((9/25:ℝ),lam-9/25)∈rankScoreSupport d.phi) :
    lineControlFeature lam∈controlFeatureSupport d := by
  apply hd.feature_mem_support_of_rankScores
    (show (9/25:ℝ)∈Icc pLo pHi by norm_num [pLo,pHi]) hgraph hgraph le_rfl

theorem lineControlFeature_coefficients {lam : ℝ} {d : LowRankData}
    (hR : primitive lam d (9/25)=quadratic lam (9/25)-d.S) :
    featureTheta lam d (lineControlFeature lam)=Certificates.LineControl.theta lam d.S ∧
    featureAlpha lam d (lineControlFeature lam)=Certificates.LineControl.alpha lam d.S := by
  constructor
  · dsimp [featureTheta,lineControlFeature,Certificates.Control.theta,Certificates.Control.det]
    rw [hR]
    norm_num [Certificates.LineControl.theta,Certificates.LineControl.denominator]
    congr 1 <;> ring
  · dsimp [featureAlpha,lineControlFeature,Certificates.Control.alphaNumerator,controlDeterminant]
    rw [hR]
    norm_num [Certificates.LineControl.alpha,Certificates.LineControl.denominator]
    congr 1 <;> ring

theorem lineControl_bound_of_all_features {phi : ℝ→ℝ} {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d)
    (hgraph : ((9/25:ℝ),lam-9/25)∈rankScoreSupport d.phi)
    (hR : primitive lam d (9/25)=quadratic lam (9/25)-d.S)
    (hcontrol : ∀ r∈Icc zStart 1,∀ v∈controlFeatureSupport d,
      phi r≤featureH hd r (curvePrimitive phi r) v) :
    ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -Certificates.LineControl.theta lam d.S*(r-lam)-Certificates.LineControl.alpha lam d.S*
        (quadratic lam (r-9/25)-d.S-curvePrimitive phi r) := by
  have hv := lineControlFeature_mem hd hgraph
  have he := lineControlFeature_coefficients hR
  intro r hr
  have hh := hcontrol r ⟨by have hh:=hr.1; norm_num [zStart] at *; linarith only [hh],hr.2⟩
    (lineControlFeature lam) hv
  rw [featureH_as_highAffineControl hd hv (curvePrimitive phi) r,he.1,he.2] at hh
  exact hh

end OptimalG.Variational
