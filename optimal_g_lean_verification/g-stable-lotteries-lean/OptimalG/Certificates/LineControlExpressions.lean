import OptimalG.FixedControlDeficit

namespace OptimalG.Certificates.LineControl
open Variational

noncomputable def denominator (lam S : ℝ) : ℝ :=
  (2*lam-9/25)*(quadratic lam (9/25)-S)-
    (18/25-lam)*(quadratic lam (16/25)-S)
noncomputable def slopeNumerator (lam S : ℝ) : ℝ :=
  (lam-9/25)*(quadratic lam (9/25)-S+quadratic lam (16/25)-S)-
    denominator lam S+(lam-9/25)*(lam+9/25)*(9/25)
noncomputable def theta (lam S : ℝ) : ℝ :=
  (lam-9/25)*(quadratic lam (9/25)-S+quadratic lam (16/25)-S)/denominator lam S
noncomputable def alpha (lam S : ℝ) : ℝ :=
  (lam-9/25)*(lam+9/25)/denominator lam S
noncomputable def slope (lam S : ℝ) : ℝ := slopeNumerator lam S/denominator lam S
noncomputable def crossing (lam S : ℝ) : ℝ :=
  lam+(lam-9/25)*(lam+9/25)*(9/25)^2/(2*slopeNumerator lam S)

theorem slope_identity {lam S : ℝ} (hD : denominator lam S≠0) :
    slope lam S=theta lam S-1+alpha lam S*(9/25) := by
  unfold slope theta alpha
  field_simp [hD]
  unfold slopeNumerator
  ring

theorem crossing_identity {lam S : ℝ}
    (hD : denominator lam S≠0) (hN : slopeNumerator lam S≠0) :
    slope lam S*(crossing lam S-lam)=alpha lam S*(9/25)^2/2 := by
  unfold slope crossing alpha
  field_simp [hD,hN]
  ring

end OptimalG.Certificates.LineControl
