import OptimalG.Certificates.StaticCurve
import OptimalG.Certificates.StaticLowSemantic
import OptimalG.Certificates.StaticMassScalars
import OptimalG.CompletedCurveFacts
import OptimalG.HighMassGeometry
import OptimalG.TinyMassApproximate

/-! Concrete shape, support-graph, tail and tiny-mass facts for the static curve. -/
namespace OptimalG.Certificates.StaticCurve
open Set Variational

theorem initial_formula : score 0=SmallMassExpressions.initial StaticLow.lam StaticLow.slack := by
  rw [initial_value]
  norm_num [SmallMassExpressions.initial,headInitial,Variational.cap,capScore,capSlope,Certificates.cap]
  <;> ring

theorem slope_formula : StaticLow.affineHeadSlope=
    SmallMassExpressions.slope StaticLow.lam StaticLow.slack := by
  norm_num [StaticLow.affineHeadSlope,SmallMassExpressions.slope,headSlope,headInitial,
    Variational.cap,capScore,capSlope,Certificates.cap]
  <;> ring

theorem mass_geometry : BinaryCurveGeometry score StaticLow.lam StaticLow.slack
    (SmallMassExpressions.slope StaticLow.lam StaticLow.slack) StaticLow.leftContact := by
  rw [←slope_formula]
  exact binaryGeometry

theorem line_782 : ∀ r∈Icc (9/25:ℝ) (391/500),score r=(StaticLow.lam:ℝ)-r := by
  intro r hr
  exact (line_values ⟨(by norm_num [StaticLow.rightContact,UpperProfileData.rightContact] :
      (StaticLow.rightContact:ℝ)≤9/25).trans hr.1,
    hr.2.trans (by norm_num [StaticHigh.departure])⟩).1

theorem score_graph {r : ℝ} (hr : r∈Icc xLo xHi) :
    (r,score r)∈rankScoreSupport staticLowData.phi := by
  have hr' : r∈Icc (0.2635:ℝ) StaticLow.lam := by
    norm_num [xLo,xHi] at hr
    norm_num [StaticLow.lam]
    constructor <;> linarith only [hr.1,hr.2]
  rw [low_score hr']
  exact staticLow_score_graph hr

theorem primitive_variational {r : ℝ} (hr : r∈Icc (527/2000:ℝ) xHi) :
    curvePrimitive score r=Variational.primitive StaticLow.lam staticLowData r := by
  have hr' : r∈Icc (0.2635:ℝ) StaticLow.lam := by
    norm_num [xHi] at hr
    norm_num [StaticLow.lam]
    exact ⟨hr.1,by linarith only [hr.2]⟩
  rw [primitive_staticLow]
  exact low_primitive hr'

theorem tail_anchor_score {r : ℝ} (hr : r∈Icc (7/8:ℝ) 1) :
    score r=tailScore (539/625) StaticMass.anchorValue StaticMass.anchorScore r := by
  rw [StaticMass.score_reanchor]
  exact (tail_values ⟨(by norm_num [StaticHigh.contact] : (StaticHigh.contact:ℝ)≤7/8).trans hr.1,hr.2⟩).1

theorem tail_anchor_primitive {r : ℝ} (hr : r∈Icc (7/8:ℝ) 1) :
    curvePrimitive score r=tailPrimitive (539/625) StaticMass.anchorValue StaticMass.anchorScore r := by
  rw [StaticMass.primitive_reanchor]
  exact (tail_values ⟨(by norm_num [StaticHigh.contact] : (StaticHigh.contact:ℝ)≤7/8).trans hr.1,hr.2⟩).2

theorem tail_cones {r : ℝ} (hr : r∈Icc (22/25:ℝ) 1) :
    -1+2*(1-r)≤score r ∧ score r≤-1+(67/10)*(1-r) := by
  rw [tail_anchor_score ⟨by linarith only [hr.1],hr.2⟩]
  exact polynomial_tail_cones (by norm_num)
    (by linarith only [StaticMass.backward_bounds.2.1])
    (by linarith only [StaticMass.backward_bounds.1.2])
    (by linarith only [StaticMass.backward_bounds.1.1,StaticMass.backward_bounds.2.2]) r hr

theorem line_deficits {r : ℝ}
    (hr : r∈Icc (StaticLow.rightContact:ℝ) StaticHigh.departure) :
    binarySlackArea score StaticLow.lam StaticLow.slack r=0 ∧
      scoreDefect score StaticLow.lam r=0 := by
  have hh := line_values hr
  change score r=_ ∧ curvePrimitive score r=_ at hh
  unfold binarySlackArea scoreDefect
  rw [hh.1,hh.2]
  simp only [Variational.quadratic,Certificates.quadratic]
  constructor <;> ring

theorem tiny_mass {p : ℝ} (hp : p∈Ioc (0:ℝ) (1/25)) :
    ThreeFunctionTest score StaticLow.lam p (tinyMassBeta score StaticLow.lam p)
      (1+tinyMassBeta score StaticLow.lam p*p) := by
  apply verifierCurve.tinyMass_test_approximate hp StaticMass.parameter_ranges.1
    (by constructor <;> linarith only [initial_bounds.1,initial_bounds.2])
  · intro u hu
    have hh := binaryGeometry.low_slope 0 u le_rfl hu.1 hu.2
    linarith only [hh]
  · intro r hr
    exact head (by convert! hr.2 using 1 <;> norm_num)
  · have hh := (cap_values (r:=(527/2000:ℝ))
      ⟨by norm_num,by norm_num [StaticLow.leftContact,UpperProfileData.leftContact]⟩).1
    rw [hh]
    norm_num [capSlope,StaticLow.lam,StaticLow.slack]
  · intro u hu
    exact tail_cones ⟨by linarith only [hu.1],hu.2⟩

end OptimalG.Certificates.StaticCurve
