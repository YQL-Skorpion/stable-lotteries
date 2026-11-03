import OptimalG.Certificates.StaticBinaryCentralExpressions
import OptimalG.Certificates.StaticHighParameters
import OptimalG.BinaryAllMass
import OptimalG.Certificates.PolynomialArithmeticHigher

namespace OptimalG.Certificates.StaticBinaryStationaryExpressions
open StaticBinaryCentralExpressions
noncomputable def headMatch (p r : ℝ) : ℝ :=
  headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r-(1-p)^2
noncomputable def capMatch (p r : ℝ) : ℝ :=
  (1-r)^2*(Variational.stationaryLevel L S r-(1-p)^2)
noncomputable def headBarrier (p r : ℝ) : ℝ :=
  p*((1-p)-headSlack L initial StaticBinaryCentralExpressions.slope r)
noncomputable def capBarrier (p r : ℝ) : ℝ := p*((1-p)-Variational.capSlack L S r)
noncomputable def HeadShift (p r : ℝ) : ℝ := r+1-p-7189/20000
noncomputable def HeadZero (p r : ℝ) : ℝ :=
  L*((1-p)-headSlack L initial StaticBinaryCentralExpressions.slope r)-
    (initial*(1-p)+StaticBinaryCentralExpressions.slope*(1-p)^2/2)
noncomputable def HeadEarlyLeft (p r : ℝ) : ℝ := Variational.quadratic L p-S-headBarrier p r
noncomputable def HeadEarlyRight (p r : ℝ) : ℝ :=
  Variational.quadratic L p-S-(399/500)*(p-391/500)^2-headBarrier p r
noncomputable def HeadLate (p r : ℝ) : ℝ :=
  1-2*p-headSlack L initial StaticBinaryCentralExpressions.slope r+p*(1-p)/(L-r)+
    Variational.capDiagonalTheta L S (29/100) (1459/5000)*(p-L)+
    Variational.capDiagonalAlpha L S (29/100) (1459/5000)*
      (Variational.quadratic L (p-29/100)-S-headBarrier p r)
noncomputable def CapShift (p r : ℝ) : ℝ := r+1-p-7189/20000
noncomputable def CapZero (p r : ℝ) : ℝ :=
  L*((1-p)-Variational.capSlack L S r)-
    (initial*(1-p)+StaticBinaryCentralExpressions.slope*(1-p)^2/2)
noncomputable def CapCurvature (p r : ℝ) : ℝ :=
  tailSlope StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore p-
    Variational.stationaryBarrierCurvature L S p r
end OptimalG.Certificates.StaticBinaryStationaryExpressions
