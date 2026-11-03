import OptimalG.SmallMassHeadExclusion

/-! Scalar certificate inputs for the attained supporting infimum. These
lemmas remove the minimizing rank from the numerical transport conditions. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem supportMinimum_ge_one {m : ℝ} (hm : lam<m) :
    1≤supportMinimum phi lam m := by
  apply h.le_supportMinimum_of_support hm
  intro x hx
  have hh := h.ceiling x ⟨hx.1,hx.2.trans h.lam_lt_one.le⟩
  linarith only [hh,hm]

theorem supportMinimum_le_of_witness {m r eta : ℝ} (hm : lam<m)
    (hr : r∈Ico (0:ℝ) lam) (hw : m-r≤eta*phi r) :
    supportMinimum phi lam m≤eta := by
  have hh := supportMinimum_le_ratio h.lam_pos
    (h.continuous.mono (Icc_subset_Icc le_rfl h.lam_lt_one.le)) h.at_lam
    (fun x hx => h.positive hx) hm hr
  exact hh.trans ((div_le_iff₀ (h.positive hr)).mpr hw)

theorem supportMinimum_minimizer_score_le_zero {x : ℝ}
    (hx : x∈Ico (0:ℝ) lam) : phi x≤phi 0 :=
  h.decreasing.antitoneOn ⟨le_rfl,h.lam_pos.le.trans h.lam_lt_one.le⟩
    ⟨hx.1,hx.2.le.trans h.lam_lt_one.le⟩ hx.1

theorem supportMinimum_minimizer_score_le_cap_of_scalars {S m slope x w : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hm : lam<m)
    (hhead : ∀ u∈Icc (0:ℝ) (527/2000),phi u=phi 0+slope*u)
    (hcap : ∀ u∈Icc (527/2000:ℝ) (7/25),phi u=Variational.capScore lam S u)
    (hw : w∈Ico (0:ℝ) lam)
    (htwo : m-w≤2*phi w)
    (hzero : (m-w)*phi 0<m*phi w)
    (hx : x∈Ico (0:ℝ) lam)
    (hmin : supportMinimum phi lam m=(m-x)/phi x) :
    phi x≤Variational.capScore lam S (7/25) := by
  have hpos := h.positive hw
  have hpos0 := h.positive ⟨le_rfl,h.lam_pos⟩
  have heup := supportMinimum_le_ratio h.lam_pos
    (h.continuous.mono (Icc_subset_Icc le_rfl h.lam_lt_one.le)) h.at_lam
    (fun y hy => h.positive hy) hm hw
  have htwobound := h.supportMinimum_le_of_witness hm hw htwo
  have hstrict : supportMinimum phi lam m*phi 0<m := by
    have hh := mul_le_mul_of_nonneg_right heup hpos0.le
    have hr : ((m-w)/phi w)*phi 0<m := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hpos).mpr hzero
    exact hh.trans_lt hr
  exact h.supportMinimum_minimizer_score_le_cap hlam hS hm
    ⟨h.supportMinimum_ge_one hm,htwobound⟩ hhead hcap hstrict hx hmin

end VerifierCurve
end OptimalG
