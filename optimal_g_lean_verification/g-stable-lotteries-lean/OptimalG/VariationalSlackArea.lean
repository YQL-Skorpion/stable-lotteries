import OptimalG.VariationalSlopeIntegration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact triangular slack-area estimates. These turn a reference integral
bound into a pointwise slack bound without assuming pointwise regularity of
the original measurable score. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem integral_slack_triangle (r eps L : ℝ) (hL : 0 < L) :
    (∫ s in r..(r+eps/L), eps-L*(s-r)) = eps^2/(2*L) := by
  have h1 : IntervalIntegrable (fun s : ℝ => L*(s-r)) volume r (r+eps/L) :=
    (by fun_prop : Continuous (fun s : ℝ => L*(s-r))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s : ℝ => s) volume r (r+eps/L) := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const h1,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub h2 intervalIntegrable_const,
    integral_id,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt hL]
  <;> ring

 theorem slack_triangle_area_lower {a b r eps L : ℝ} {f : ℝ → ℝ}
    (hL : 0 < L) (heps : 0 ≤ eps) (hr : r ∈ Icc a b)
    (ht : r+eps/L ≤ b) (hf : IntervalIntegrable f volume a b)
    (hnonneg : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ f s)
    (hlower : ∀ᵐ s ∂volume.restrict (Icc r (r+eps/L)), eps-L*(s-r) ≤ f s) :
    eps^2/(2*L) ≤ ∫ s in a..b,f s := by
  have hrt : r ≤ r+eps/L := by linarith [div_nonneg heps hL.le]
  have hsub : Icc r (r+eps/L) ⊆ Icc a b := Icc_subset_Icc hr.1 ht
  have hfi : IntervalIntegrable f volume r (r+eps/L) :=
    hf.mono_set (by simpa only [uIcc_of_le hrt,uIcc_of_le (hr.1.trans hr.2)] using hsub)
  have hh := intervalIntegral.integral_mono_ae_restrict hrt
    ((continuous_const.sub ((continuous_id.sub continuous_const).const_mul L)).intervalIntegrable _ _)
    hfi hlower
  change (∫ s in r..r+eps/L,eps-L*(s-r)) ≤ ∫ s in r..r+eps/L,f s at hh
  rw [integral_slack_triangle r eps L hL] at hh
  apply hh.trans
  rw [intervalIntegral.integral_of_le hrt,intervalIntegral.integral_of_le (hr.1.trans hr.2)]
  exact setIntegral_mono_set hf.1 (by
    rw [restrict_Ioc_eq_restrict_Icc]
    filter_upwards [hnonneg] with s hs
    exact hs)
    (Eventually.of_forall (Ioc_subset_Ioc hr.1 ht))

 theorem slack_lt_of_area_bound {a b r eps L : ℝ} {f : ℝ → ℝ}
    (hL : 0 < L) (heps : 0 ≤ eps) (hr : r ∈ Icc a b)
    (ht : r+eps/L ≤ b) (hf : IntervalIntegrable f volume a b)
    (hnonneg : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ f s)
    (hincrement : ∀ s ∈ Icc r (r+eps/L), f r-L*(s-r) ≤ f s)
    (harea : (∫ s in a..b,f s) < eps^2/(2*L)) : f r < eps := by
  by_contra hn
  have hle := le_of_not_gt hn
  have hh := slack_triangle_area_lower hL heps hr ht hf hnonneg (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    linarith [hincrement s hs])
  exact (not_le_of_gt harea) hh

 theorem score_slack_lower_increment_of_antitone {lam a b r s : ℝ} {psi : ℝ → ℝ}
    (hm : AntitoneOn psi (Icc a b)) (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r ≤ s) :
    (lam-r-psi r)-(s-r) ≤ lam-s-psi s := by
  linarith [hm hr hs hrs]

end OptimalG.Variational
