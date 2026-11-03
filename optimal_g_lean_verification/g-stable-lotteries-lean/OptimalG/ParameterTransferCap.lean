import OptimalG.Certificates.VariationalBridge

/-! The explicit upward parameter perturbation retains the root and cap
inequalities. This competitor does not require equality at the left cap. -/
namespace OptimalG.Variational.ParameterTransfer
open Set

noncomputable def gain (delta r : ℝ) : ℝ := 0.1788*delta+delta*max 0 (r-0.38)
noncomputable def scalar (S delta : ℝ) : ℝ := S+0.2012*delta
noncomputable def shifted (J : ℝ → ℝ) (delta r : ℝ) : ℝ := J r+gain delta r

theorem gain_before {delta r : ℝ} (hr : r ≤ 0.38) : gain delta r=0.1788*delta := by
  simp [gain,max_eq_left (show r-0.38 ≤ 0 by linarith)]

theorem gain_after {delta r : ℝ} (hr : 0.38 ≤ r) : gain delta r=delta*(r-0.2012) := by
  rw [gain,max_eq_right (show 0 ≤ r-0.38 by linarith)]
  ring

theorem gain_nonneg {delta r : ℝ} (hd : 0 ≤ delta) : 0 ≤ gain delta r := by
  unfold gain
  positivity

theorem gain_monotone {delta : ℝ} (hd : 0 ≤ delta) : Monotone (gain delta) := by
  intro a b hab
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (max_le_max le_rfl (sub_le_sub_right hab _)) hd)

theorem shifted_monotoneOn {J : ℝ → ℝ} {s : Set ℝ} {delta : ℝ}
    (hJ : MonotoneOn J s) (hd : 0 ≤ delta) : MonotoneOn (shifted J delta) s := by
  intro a ha b hb hab
  exact add_le_add (hJ ha hb hab) (gain_monotone hd hab)

theorem shifted_root {lam S delta r : ℝ} {J : ℝ → ℝ}
    (hd : 0 ≤ delta) (hroot : quadratic lam r-S ≤ J r) :
    quadratic (lam+delta) r-scalar S delta ≤ shifted J delta r := by
  have hg := le_max_right (0 : ℝ) (r-0.38)
  have hp := mul_le_mul_of_nonneg_left hg hd
  unfold shifted gain scalar quadratic at *
  nlinarith

theorem shifted_flat {lam S delta r : ℝ} {J : ℝ → ℝ}
    (hr : 0.38 ≤ r) (hflat : J r=quadratic lam r-S) :
    shifted J delta r=quadratic (lam+delta) r-scalar S delta := by
  rw [shifted,gain_after hr,hflat]
  unfold quadratic scalar
  ring

theorem scalar_slackUpper {lam S delta : ℝ} (hd : 0 ≤ delta)
    (hS : S ≤ slackUpper lam) : scalar S delta ≤ slackUpper (lam+delta) := by
  unfold scalar slackUpper at *
  linarith

theorem cap_gain_identity (lam S delta r : ℝ) (hr : r ≠ 1) :
    cap (lam+delta) (scalar S delta) r-cap lam S r-gain delta r =
      delta*(2*lam-0.6788+r/2-max 0 (r-0.38)-(S+0.2012*lam)/(1-r))+
        delta^2*(1-0.2012/(1-r)) := by
  have hden : 1-r ≠ 0 := sub_ne_zero.mpr hr.symm
  unfold cap scalar gain
  field_simp [hden]
  ring

/-- A strict quantitative cap improvement for every rank in the low interval. -/
theorem cap_gain_lower {lam S delta r : ℝ}
    (hL : Certificates.Compact.LambdaRange lam) (hS : S ≤ 0.026651)
    (hd : 0 ≤ delta) (hr : r ∈ Icc (0.25 : ℝ) 0.385) :
    0.338*delta ≤ cap (lam+delta) (scalar S delta) r-cap lam S r-gain delta r := by
  have hden : 0 < 1-r := by linarith [hr.2]
  have hfrac : (S+0.2012*lam)/(1-r) ≤ 0.23 := by
    apply (div_le_iff₀ hden).mpr
    linarith [hL.2,hr.2]
  have hrank : 0.125 ≤ r/2-max 0 (r-0.38) := by
    by_cases hh : r ≤ 0.38
    · rw [max_eq_left (show r-0.38 ≤ 0 by linarith)]
      linarith [hr.1]
    · rw [max_eq_right (show 0 ≤ r-0.38 by linarith)]
      linarith [hr.2]
  have hlinear : 0.338 ≤ 2*lam-0.6788+r/2-max 0 (r-0.38)-(S+0.2012*lam)/(1-r) := by
    linarith [hL.1]
  have hquad : 0 ≤ 1-0.2012/(1-r) := by
    have hh : (0.2012 : ℝ)/(1-r) ≤ 1 := (div_le_iff₀ hden).mpr (by linarith [hr.2])
    linarith
  rw [cap_gain_identity lam S delta r (by linarith [hr.2])]
  have hh := mul_le_mul_of_nonneg_left hlinear hd
  have hq := mul_nonneg (sq_nonneg delta) hquad
  nlinarith

theorem shifted_cap {lam S delta r : ℝ} {J : ℝ → ℝ}
    (hL : Certificates.Compact.LambdaRange lam) (hS : S ≤ 0.026651)
    (hd : 0 ≤ delta) (hr : r ∈ Icc (0.25 : ℝ) 0.385)
    (hcap : J r ≤ cap lam S r) :
    shifted J delta r ≤ cap (lam+delta) (scalar S delta) r := by
  have hh := cap_gain_lower hL hS hd hr
  have hp : 0 ≤ (0.338 : ℝ)*delta := mul_nonneg (by norm_num) hd
  unfold shifted
  linarith

end OptimalG.Variational.ParameterTransfer
