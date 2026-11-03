import OptimalG.Certificates.StaticHighParameters
import OptimalG.Certificates.SmallMassExpressions
import OptimalG.VariationalCapControl
import OptimalG.TailReanchor

/-! Exact fixed-candidate scalar margins and the terminal polynomial at the
common anchor. These are rational calculations, not extrapolated flow bounds. -/
namespace OptimalG.Certificates.StaticMass
open Set Variational
set_option maxHeartbeats 0

noncomputable def anchorValue : ℝ := tailPrimitive StaticHigh.contact
  StaticHigh.contactValue StaticHigh.contactScore (539/625)
noncomputable def anchorScore : ℝ := tailScore StaticHigh.contact
  StaticHigh.contactValue StaticHigh.contactScore (539/625)

theorem parameter_ranges :
    (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000) ∧
    (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000) := by
  norm_num [StaticLow.lam,StaticLow.slack]

theorem fixed_cap_margins :
    0<capDiagonalAlpha StaticLow.lam StaticLow.slack (27/100) (1459/5000) ∧
    (13/50:ℝ)<capDiagonalTheta StaticLow.lam StaticLow.slack (27/100) (1459/5000)-1+
      capDiagonalAlpha StaticLow.lam StaticLow.slack (27/100) (1459/5000)*(27/100) ∧
    0<(capDiagonalTheta StaticLow.lam StaticLow.slack (27/100) (1459/5000)-1+
      capDiagonalAlpha StaticLow.lam StaticLow.slack (27/100) (1459/5000)*(27/100))*
        (789/1000-(StaticLow.lam:ℝ))-
      capDiagonalAlpha StaticLow.lam StaticLow.slack (27/100) (1459/5000)*(27/100)^2/2 := by
  norm_num [capDiagonalAlpha,capDiagonalTheta,Variational.cap,capScore,Variational.quadratic,StaticLow.lam,StaticLow.slack]

theorem anchor_bounds :
    anchorValue∈Icc (8793/100000:ℝ) (221/2500) ∧
    anchorScore∈Icc (-3589/10000:ℝ) (-1757/5000) := by
  norm_num [anchorValue,anchorScore,tailPrimitive,tailScore,tailCoord,tailOne,tailTwo,
    StaticHigh.contact,StaticHigh.contactValue,StaticHigh.contactScore]

theorem backward_coefficients :
    tailBackwardSlope (539/625) anchorValue anchorScore=(StaticHigh.tailSlope:ℝ) ∧
    tailBackwardCurvature (539/625) anchorValue anchorScore=(StaticHigh.tailCurvature:ℝ) := by
  have hh := tailBackwardCoefficients_reanchor
    (a:=(539/625:ℝ)) (z:=(StaticHigh.contact:ℝ))
    (Y:=(StaticHigh.contactValue:ℝ)) (H:=(StaticHigh.contactScore:ℝ))
    (by norm_num) (by norm_num [StaticHigh.contact])
  change tailBackwardSlope (539/625) anchorValue anchorScore=_ ∧
    tailBackwardCurvature (539/625) anchorValue anchorScore=_ at hh
  rw [hh.1,hh.2]
  norm_num [tailBackwardSlope,tailBackwardCurvature,tailOne,tailTwo,
    StaticHigh.contact,StaticHigh.contactValue,StaticHigh.contactScore,
    StaticHigh.tailSlope,StaticHigh.tailCurvature]

theorem backward_bounds :
    tailBackwardSlope (539/625) anchorValue anchorScore∈Icc (309/50:ℝ) (321/50) ∧
    tailBackwardCurvature (539/625) anchorValue anchorScore∈Icc (1077/100:ℝ) (1273/100) := by
  rw [backward_coefficients.1,backward_coefficients.2]
  norm_num [StaticHigh.tailSlope,StaticHigh.tailCurvature]

theorem score_reanchor (r : ℝ) :
    tailScore (539/625) anchorValue anchorScore r=
      tailScore StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r :=
  tailScore_reanchor (by norm_num) (by norm_num [StaticHigh.contact]) r

theorem primitive_reanchor (r : ℝ) :
    tailPrimitive (539/625) anchorValue anchorScore r=
      tailPrimitive StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore r :=
  tailPrimitive_reanchor (by norm_num) (by norm_num [StaticHigh.contact]) r

end OptimalG.Certificates.StaticMass
