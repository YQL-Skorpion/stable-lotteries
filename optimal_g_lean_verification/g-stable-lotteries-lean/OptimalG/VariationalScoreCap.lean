import OptimalG.VariationalSlopeBounds
import OptimalG.VariationalCompletedCurve

/-! The free score stays below the tangent cap score because its finite
fall is stronger than the cap curvature. This is a pointwise consequence of
the recovered curve, independent of any supporting-control activity. -/
namespace OptimalG.Variational
open Set

theorem Admissible.capRegularScore_le_initialCap {lam c : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} (hd : Admissible lam d) (hc : c∈Icc ell xHi)
    (hjoin : psi c=capScore lam d.S c) (hanti : AntitoneOn psi (Icc c xHi)) :
    ∀ r∈Icc ell xHi,capRegularScore lam d.S c psi r≤capScore lam d.S ell := by
  have hcap : AntitoneOn (capScore lam d.S) (Icc ell xHi) :=
    (capScore_strictAntiOn (by linarith [hd.compact_lambdaRange.1])
      (by linarith [hd.slack_lower]) (by norm_num [xHi])).antitoneOn
  intro r hr
  by_cases hrc : r≤c
  · rw [capRegularScore_left _ _ _ _ hrc]
    exact hcap ⟨le_rfl,hr.1.trans hr.2⟩ hr hr.1
  · rw [capRegularScore_right hjoin (le_of_not_ge hrc)]
    have hh := hanti ⟨le_rfl,hc.2⟩ ⟨le_of_not_ge hrc,hr.2⟩ (le_of_not_ge hrc)
    rw [hjoin] at hh
    exact hh.trans (hcap ⟨le_rfl,hc.1.trans hc.2⟩ hc hc.1)

theorem Admissible.freeScore_le_capScore {lam c theta : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} (hd : Admissible lam d) (htheta : (0.126:ℝ) ≤ theta)
    (hjoin : psi c=capScore lam d.S c)
    (hfall : ∀ r ∈ Icc c xHi,psi r-psi c ≤ -theta*(r-c)) :
    ∀ r ∈ Icc c xHi,psi r ≤ capScore lam d.S r := by
  intro r hr
  have hcap := hd.capScore_lower_increment_uniform hr.1 hr.2
  have hs := hfall r hr
  have hm := mul_le_mul_of_nonneg_right htheta (sub_nonneg.mpr hr.1)
  rw [hjoin] at hs
  linarith

theorem Admissible.capRegularScore_le_capScore {lam c theta : ℝ} {d : LowRankData}
    {psi : ℝ → ℝ} (hd : Admissible lam d) (htheta : (0.126:ℝ) ≤ theta)
    (hjoin : psi c=capScore lam d.S c)
    (hfall : ∀ r ∈ Icc c xHi,psi r-psi c ≤ -theta*(r-c)) :
    ∀ r ≤ xHi,capRegularScore lam d.S c psi r ≤ capScore lam d.S r := by
  intro r hr
  by_cases hrc : r≤c
  · rw [capRegularScore_left _ _ _ _ hrc]
  · rw [capRegularScore_right hjoin (le_of_not_ge hrc)]
    exact hd.freeScore_le_capScore htheta hjoin hfall r ⟨le_of_not_ge hrc,hr⟩

theorem completedVariationalScore_le_capScore {lam a b c theta : ℝ} {d : LowRankData}
    {psi Y : ℝ → ℝ} (hd : Admissible lam d) (ha : 0<a) (hax : a≤xHi)
    (hb : zStart≤b) (htheta : (0.126:ℝ)≤theta)
    (hjoin : psi c=capScore lam d.S c)
    (hfall : ∀ r ∈ Icc c xHi,psi r-psi c≤-theta*(r-c)) :
    ∀ r ∈ Icc a xHi,
      completedVariationalScore a lam d (capRegularScore lam d.S c psi) Y b r≤capScore lam d.S r := by
  intro r hr
  rw [completedVariationalScore_low ha hax hb hr]
  exact hd.capRegularScore_le_capScore htheta hjoin hfall r hr.2

end OptimalG.Variational
