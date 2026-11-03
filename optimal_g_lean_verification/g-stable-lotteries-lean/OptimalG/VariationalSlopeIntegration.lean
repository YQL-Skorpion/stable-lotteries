import OptimalG.VariationalRecovery
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Integrating the almost-everywhere slope bounds used in B.3 Step 4.
The hypotheses concern the actual derivative of an actual Lipschitz function. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem lipschitz_increment_le_of_deriv_le_ae {a b k : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a b))
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv f r ≤ k)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    f y-f x ≤ k*(y-x) := by
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hLip : LipschitzOnWith K f (uIcc x y) := by
    rw [uIcc_of_le hxy]
    exact hf.mono hsub
  have hAC := hLip.absolutelyContinuousOnInterval
  have hi := intervalIntegral.integral_mono_ae_restrict hxy hAC.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => k) volume x y)
    (ae_restrict_of_ae_restrict_of_subset hsub hd)
  rw [hAC.integral_deriv_eq_sub,intervalIntegral.integral_const] at hi
  simpa only [smul_eq_mul,mul_comm] using hi

theorem lipschitz_antitone_of_deriv_nonpos_ae {a b : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a b))
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), deriv f r ≤ 0) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hh := lipschitz_increment_le_of_deriv_le_ae hf hd hx hy hxy
  simpa only [zero_mul,sub_nonpos] using hh

theorem lipschitz_nonnegative_slack_antitone {a b gamma : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a b)) (hgamma : 0 ≤ gamma)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ f r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), 0 < f r → deriv f r ≤ -gamma) :
    AntitoneOn f (Icc a b) := by
  apply lipschitz_antitone_of_deriv_nonpos_ae hf
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hd] with r hr hder
  by_cases hfr : 0 < f r
  · linarith [hder hfr]
  · have hz : f r = 0 := le_antisymm (le_of_not_gt hfr) (hpos r ⟨hr.1.le,hr.2.le⟩)
    have hm : IsMinOn f (Icc a b) r := by
      intro s hs
      change f r ≤ f s
      rw [hz]
      exact hpos s hs
    exact (hm.isLocalMin (Icc_mem_nhds hr.1 hr.2)).deriv_eq_zero.le

/-- A nonnegative Lipschitz slack whose derivative is at most -gamma while
positive obeys the exact linear extinction bound. -/
theorem lipschitz_nonnegative_slack_decay {a b gamma : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a b)) (hgamma : 0 ≤ gamma)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ f r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), 0 < f r → deriv f r ≤ -gamma) :
    ∀ t ∈ Icc a b, f t ≤ max 0 (f a-gamma*(t-a)) := by
  have hm := lipschitz_nonnegative_slack_antitone hf hgamma hpos hd
  intro t ht
  by_cases hft : 0 < f t
  · have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
    have hbound : ∀ᵐ r ∂volume.restrict (Icc a t), deriv f r ≤ -gamma := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae_restrict_of_subset hsub hd]
        with r hr hder
      exact hder (hft.trans_le (hm (hsub hr) ht hr.2))
    have hinc := lipschitz_increment_le_of_deriv_le_ae (hf.mono hsub) hbound
      (show a ∈ Icc a t from ⟨le_rfl,ht.1⟩) (show t ∈ Icc a t from ⟨ht.1,le_rfl⟩) ht.1
    have hh : f t ≤ f a-gamma*(t-a) := by linarith
    exact hh.trans (le_max_right _ _)
  · have hz : f t = 0 := le_antisymm (le_of_not_gt hft) (hpos t ht)
    rw [hz]
    exact le_max_left _ _

theorem lipschitz_nonnegative_slack_extinct {a b gamma t : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc a b)) (hgamma : 0 ≤ gamma)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ f r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b), 0 < f r → deriv f r ≤ -gamma)
    (ht : t ∈ Icc a b) (htime : f a ≤ gamma*(t-a)) : f t = 0 := by
  have hh := lipschitz_nonnegative_slack_decay hf hgamma hpos hd t ht
  rw [max_eq_left (sub_nonpos.mpr htime)] at hh
  exact le_antisymm hh (hpos t ht)

end OptimalG.Variational
