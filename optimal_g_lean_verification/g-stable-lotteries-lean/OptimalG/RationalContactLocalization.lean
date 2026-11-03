import OptimalG.HeadStationaryCurve
import OptimalG.RationalStationaryCurve

/-! Scalar entry-level checks and actual terminal tangencies locate the
contact rank without assuming the binary inequality being established. -/
namespace OptimalG
open Set Variational

/-- The full admissible scalar rectangle already gives a uniform rational
slope gap, without a numerical interval certificate. -/
theorem capSlopeGap_lower {lam S r : ℝ} (hl : lam≤3/5)
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ)) (hr : r≤31/100) :
    (89/100:ℝ)≤capSlopeGap lam S r := by
  have hden0 : 0<(1-r)^3 := pow_pos (by linarith only [hr]) _
  have hden : (69/100:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hr]) _
  have hprod := mul_le_mul hl hS.2 hS.1 (by norm_num : (0:ℝ)≤3/5)
  have hfrac : 2*lam*S/(1-r)^3≤11/100 := by
    apply (div_le_iff₀ hden0).mpr
    norm_num at hden
    nlinarith only [hden,hprod]
  unfold capSlopeGap
  linarith only [hfrac]

/-- A convenient fixed growth constant for actual stationary inverses. -/
theorem capStationarySlope_lower {lam S r : ℝ} (hl : lam ∈ Icc (11/20:ℝ) (3/5:ℝ))
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ)) (hr : r≤31/100) :
    (2/5:ℝ)≤2*(lam-r)*capSlopeGap lam S r := by
  have hg := capSlopeGap_lower hl.2 hS hr
  have hh : (12/25:ℝ)≤2*(lam-r) := by linarith only [hl.1,hr]
  have hm := mul_le_mul hh hg (by norm_num : (0:ℝ)≤89/100) (by linarith only [hh])
  norm_num at hm
  linarith only [hm]

/-- Two scalar endpoint checks construct an interior head-entry mass. -/
theorem exists_mass_for_square_level {a b L : ℝ} (hab : a≤b)
    (hleft : L<(1-a)^2) (hright : (1-b)^2<L) :
    ∃ p ∈ Ioo a b,(1-p)^2=L := by
  obtain ⟨p,hp,he⟩ := intermediate_value_Icc (f:=fun p : ℝ => -(1-p)^2) hab
    (by fun_prop) (show -L ∈ Icc (-(1-a)^2) (-(1-b)^2) from ⟨by linarith,by linarith⟩)
  have hmatch : (1-p)^2=L := by linarith only [he]
  have hpa : p≠a := by intro hh; subst p; linarith only [hleft,hmatch]
  have hpb : p≠b := by intro hh; subst p; linarith only [hright,hmatch]
  exact ⟨p,⟨lt_of_le_of_ne hp.1 hpa.symm,lt_of_le_of_ne hp.2 hpb⟩,hmatch⟩

/-- The head and rational stationary levels agree at an actual C¹ join. -/
theorem headStationaryLevel_eq_cap {lam S phi0 slope xh : ℝ}
    (hvalue : cap lam S xh=phi0*xh+slope*xh^2/2)
    (hscore : capScore lam S xh=phi0+slope*xh) :
    headStationaryLevel lam S phi0 slope xh=stationaryLevel lam S xh := by
  unfold headStationaryLevel headStationaryConstant stationaryLevel capSlack capDeficit
  rw [hvalue,hscore]
  unfold quadratic
  ring

/-- Positivity of the explicit rational slope gap makes the stationary level
strictly decreasing over the entire terminal rank interval. -/
theorem stationaryLevel_strictAntiOn {lam S a b : ℝ}
    (hbl : b<lam) (hb1 : b<1)
    (hgap : ∀ r ∈ Icc a b,0<capSlopeGap lam S r) :
    StrictAntiOn (stationaryLevel lam S) (Icc a b) := by
  have hd (r : ℝ) (hr : r ∈ Icc a b) := stationaryLevel_hasDerivAt lam S r
    (ne_of_lt (hr.2.trans_lt hb1))
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun r hr => (hd r hr).continuousAt.continuousWithinAt)
  intro r hr
  have hrc := interior_subset hr
  rw [(hd r hrc).deriv]
  have hp : 0<(lam-r)*capSlopeGap lam S r :=
    mul_pos (sub_pos.mpr (hrc.2.trans_lt hbl)) (hgap r hrc)
  nlinarith only [hp]

/-- Once contact occurs after entry, the actual stationary tangency cannot
lie to the left of the rational piece. -/
theorem contact_rank_ge_entry {lam S a xh b z q : ℝ}
    (hax : a≤xh) (hxl : xh<lam) (hx1 : xh<1)
    (hgap : ∀ r ∈ Icc a xh,0<capSlopeGap lam S r)
    (hqa : a≤q) (hbz : b≤z) (hz1 : z≤1)
    (hentry : stationaryLevel lam S xh=(1-b)^2)
    (hcontact : stationaryLevel lam S q=(1-z)^2) : xh≤q := by
  by_contra hn
  have hqx : q<xh := lt_of_not_ge hn
  have hanti := stationaryLevel_strictAntiOn hxl hx1 hgap
  have hh := hanti ⟨hqa,hqx.le⟩ ⟨hax,le_rfl⟩ hqx
  rw [hentry,hcontact] at hh
  have hsq : (1-z)^2≤(1-b)^2 :=
    (sq_le_sq₀ (by linarith only [hz1]) (by linarith only [hbz,hz1])).mpr (by linarith only [hbz])
  linarith only [hh,hsq]

/-- A single rational endpoint check supplies the upper contact-rank bound
from the genuine stationary equation and the right mass endpoint. -/
theorem contact_rank_lt_cutoff {lam S a qmax b q z zend : ℝ}
    (hab : qmax≤b) (hbl : b<lam) (hb1 : b<1)
    (hgap : ∀ r ∈ Icc a b,0<capSlopeGap lam S r)
    (hq : q ∈ Icc a b) (hqa : a≤qmax) (hzz : z<zend) (hzend : zend≤1)
    (hcut : stationaryLevel lam S qmax≤(1-zend)^2)
    (hcontact : stationaryLevel lam S q=(1-z)^2) : q<qmax := by
  by_contra hn
  have hqq : qmax≤q := le_of_not_gt hn
  have hh := (stationaryLevel_strictAntiOn hbl hb1 hgap).antitoneOn
    ⟨hqa,hab⟩ hq hqq
  rw [hcontact] at hh
  have hsq : (1-zend)^2<(1-z)^2 :=
    (sq_lt_sq₀ (by linarith only [hzend]) (by linarith only [hzz,hzend])).mpr (by linarith only [hzz])
  linarith only [hh,hcut,hsq]

end OptimalG
