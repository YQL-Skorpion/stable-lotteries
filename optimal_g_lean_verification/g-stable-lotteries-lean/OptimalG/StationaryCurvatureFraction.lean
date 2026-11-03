import OptimalG.RationalStationaryCurve

namespace OptimalG.Variational

/-- A single positive-denominator form avoids nested rational expressions in
fixed stationary-curvature certificates. -/
theorem stationaryBarrierCurvature_fraction (lam S p r : ℝ)
    (hr1 : r≠1) (hrL : r≠lam) (hgap : (1-r)^3-2*lam*S≠0) :
    stationaryBarrierCurvature lam S p r=
      (-2*(lam-r)^3*((1-r)^3-2*lam*S)+
        (2-3*p)*(lam-r)^2*((1-r)^3-2*lam*S)+p*(1-p)^2*(1-r)^3)/
      ((lam-r)^3*((1-r)^3-2*lam*S)) := by
  have h1 : 1-r≠0 := sub_ne_zero.mpr hr1.symm
  have hL : lam-r≠0 := sub_ne_zero.mpr hrL.symm
  have hg : capSlopeGap lam S r=((1-r)^3-2*lam*S)/(1-r)^3 := by
    unfold capSlopeGap
    field_simp
  unfold stationaryBarrierCurvature
  rw [hg]
  field_simp [h1,hL,hgap]
  <;> ring

end OptimalG.Variational
