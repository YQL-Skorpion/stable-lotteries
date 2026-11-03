import OptimalG.VariationalContactContinuity
import OptimalG.VariationalUniformRightSlope
import OptimalG.VariationalReferenceGrowth

/-! The cap-deficit argument which excludes an early last contact. All
numerical inputs (support slope, cap curvature, and reference deficit) are
explicit; the integration and endpoint comparison are proved analytically. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem capScore_lower_of_curvature {lam S a b K : ℝ}
    (hab : a ≤ b) (hb : b < 1)
    (hcurv : ∀ r ∈ Icc a b, -K ≤ -2*lam*S/(1-r)^3) :
    ∀ r ∈ Icc a b, capScore lam S a-K*(r-a) ≤ capScore lam S r := by
  have hder : ∀ r ∈ Icc a b, HasDerivAt (capScore lam S) (-2*lam*S/(1-r)^3) r := by
    intro r hr
    exact capScore_hasDerivAt lam S r (ne_of_lt (hr.2.trans_lt hb))
  have hgrow := reference_primitive_lower_increment hder
    (fun r hr => hcurv r ⟨hr.1.le,hr.2.le⟩)
  intro r hr
  have h := hgrow a ⟨le_rfl,hab⟩ r hr hr.1
  nlinarith only [h]

 theorem cap_gap_from_right_slope {lam S a b theta K : ℝ} {psi : ℝ → ℝ}
    (hab : a ≤ b) (hb : b < 1) (hpsi : Continuous psi)
    (hscore : ∀ r ∈ Icc a b, psi r ≤ capScore lam S a-theta*(r-a))
    (hcurv : ∀ r ∈ Icc a b, -K ≤ -2*lam*S/(1-r)^3) :
    ((theta-K)/2)*(b-a)^2 ≤ cap lam S b-(cap lam S a+∫ r in a..b,psi r) := by
  let D := fun r => cap lam S r-(cap lam S a+∫ t in a..r,psi t)-((theta-K)/2)*(r-a)^2
  have hDslope (r : ℝ) (hr : r ∈ Icc a b) :
      HasDerivAt D (capScore lam S r-psi r-(theta-K)*(r-a)) r := by
    have hint := (intervalIntegral.integral_hasDerivAt_right (hpsi.intervalIntegrable a r)
      (hpsi.stronglyMeasurableAtFilter volume (𝓝 r)) hpsi.continuousAt).const_add (cap lam S a)
    have h := ((cap_hasDerivAt lam S r (ne_of_lt (hr.2.trans_lt hb))).sub hint).sub
      ((((hasDerivAt_id r).sub_const a).pow 2).const_mul ((theta-K)/2))
    convert! h using 1 <;> simp [D,Pi.sub_apply,Pi.pow_apply] <;> ring
  have hmono : MonotoneOn D (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun r hr => (hDslope r hr).continuousAt.continuousWithinAt)
    · intro r hr
      exact (hDslope r (interior_subset hr)).hasDerivWithinAt
    · intro r hr
      have hr' : r ∈ Icc a b := interior_subset hr
      have hcap := capScore_lower_of_curvature hab hb hcurv r hr'
      have hs := hscore r hr'
      nlinarith only [hcap,hs]
  have h := hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  dsimp [D] at h
  simp only [intervalIntegral.integral_same,sub_self,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at h
  linarith only [h]

 theorem contact_after_safe_of_cap_deficit {c safe reference theta K gap : ℝ}
    (horder : c ≤ reference) (hsafe : safe < reference) (hcurvature : K < theta)
    (hlower : ((theta-K)/2)*(reference-c)^2 ≤ gap)
    (hupper : gap < ((theta-K)/2)*(reference-safe)^2) : safe < c := by
  by_contra hn
  have hc : c ≤ safe := le_of_not_gt hn
  have hsq : (reference-safe)^2 ≤ (reference-c)^2 := by
    have h1 : 0 ≤ reference-safe := sub_nonneg.mpr hsafe.le
    have h2 : reference-safe ≤ reference-c := by linarith
    nlinarith only [h1,h2,sq_nonneg (safe-c)]
  have hh := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ (theta-K)/2)
  linarith

end OptimalG.Variational
