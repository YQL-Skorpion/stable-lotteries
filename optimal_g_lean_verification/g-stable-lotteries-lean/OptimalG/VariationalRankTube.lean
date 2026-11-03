import OptimalG.VariationalCapSlope

/-! Rational endpoint inequalities certify matched-rank tubes directly.
No square-root formula or external inverse-function approximation is trusted. -/
namespace OptimalG.Variational
open Set

theorem Admissible.cap_strictMono_low {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : StrictMonoOn (cap lam d.S) (Icc ell tEnd) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ell tEnd) (cap_continuous_lowInterval lam d.S)
  intro r hr
  have hr' := interior_subset hr
  have hr1 : r≠1 := by have hh := hr'.2; norm_num [tEnd] at hh; linarith only [hh]
  rw [(cap_hasDerivAt lam d.S r hr1).deriv]
  exact hd.capScore_pos hr'

theorem Admissible.quadratic_strictMono_low {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : StrictMonoOn (quadratic lam) (Icc ell tEnd) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc ell tEnd)
    (by unfold quadratic; fun_prop)
  intro r hr
  rw [(quadratic_hasDerivAt lam r).deriv]
  have hr' := (interior_subset hr).2
  have hl := hd.1.1
  norm_num [lambdaLo,tEnd] at hl hr'
  linarith only [hl,hr']

theorem Admissible.rank_lower_of_cap_endpoint {lam lo r sigma : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hlo : lo∈Icc ell tEnd) (hr : r∈Icc ell tEnd)
    (hsigma : sigma≤cap lam d.S r) (hgap : cap lam d.S lo≤sigma) : lo≤r := by
  by_contra hn
  have hh := hd.cap_strictMono_low hr hlo (lt_of_not_ge hn)
  linarith only [hh,hsigma,hgap]

theorem Admissible.rank_upper_of_quadratic_endpoint {lam hi r sigma : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hhi : hi∈Icc ell tEnd) (hr : r∈Icc ell tEnd)
    (hsigma : quadratic lam r-d.S≤sigma) (hgap : sigma≤quadratic lam hi-d.S) : r≤hi := by
  by_contra hn
  have hh := hd.quadratic_strictMono_low hhi hr (lt_of_not_ge hn)
  linarith only [hh,hsigma,hgap]

theorem Admissible.matched_rank_tube {lam c rc lo hi r sigma : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : ell≤c) (hrc : rc≤tEnd)
    (hr : r∈Icc c rc) (hlo : lo∈Icc c rc) (hhi : hi∈Icc c rc)
    (hsigmaLow : quadratic lam r-d.S≤sigma) (hsigmaHigh : sigma≤cap lam d.S r)
    (hgapLow : lo=c ∨ cap lam d.S lo≤sigma)
    (hgapHigh : hi=rc ∨ sigma≤quadratic lam hi-d.S) : r∈Icc lo hi := by
  have hr' : r∈Icc ell tEnd := ⟨hc.trans hr.1,hr.2.trans hrc⟩
  constructor
  · rcases hgapLow with he | hg
    · simpa only [he] using hr.1
    · exact hd.rank_lower_of_cap_endpoint ⟨hc.trans hlo.1,hlo.2.trans hrc⟩ hr' hsigmaHigh hg
  · rcases hgapHigh with he | hg
    · simpa only [he] using hr.2
    · exact hd.rank_upper_of_quadratic_endpoint ⟨hc.trans hhi.1,hhi.2.trans hrc⟩ hr' hsigmaLow hg

end OptimalG.Variational
