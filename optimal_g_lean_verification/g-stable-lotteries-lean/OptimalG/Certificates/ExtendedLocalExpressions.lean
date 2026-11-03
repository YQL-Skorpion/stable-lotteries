import OptimalG.ExtendedHighAlgebra

/-! Exact zero-split high-transport slope for extended masses. The high
primitive deficit is retained as a variable, so two endpoint certificates
suffice for its whole permitted interval. -/
namespace OptimalG.Certificates.ExtendedLocalExpressions
open Variational ExtendedScalarExpressions

noncomputable def localCore (lam S p t z e : ℝ) : ℝ :=
  (extendedNIncrement lam S (9/25) p t*etaNumerator lam S (9/25) t-
      extendedDIncrement lam S (9/25) p t*denominator lam S (9/25) t)*(z-lam)+
    betaNumerator lam p t*etaNumerator lam S (9/25) t*(z-lam-9/25-(p-9/25)/2)+
    extendedWeightDifference lam S (9/25) p t*((9/25)*(z-lam-(9/25)/2)+e)

theorem zero_split_identity (lam S p t z e : ℝ) :
    extendedCompareCore lam S (9/25) p t 0 z e 0 0=
      (p-9/25)*localCore lam S p t z e := by
  unfold extendedCompareCore localCore
  ring

theorem deficit_affine (lam S p t z e : ℝ) :
    (17/5000)*localCore lam S p t z e=
      ((17/5000)-e)*localCore lam S p t z 0+
      e*localCore lam S p t z (17/5000) := by
  unfold localCore
  ring

end OptimalG.Certificates.ExtendedLocalExpressions
