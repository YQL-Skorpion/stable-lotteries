import OptimalG.VariationalFrozenLimit

/-!
# Closedness and attainment of the variational feasible set

The essential infimum need not converge under weak-* limits. Instead, every
continuation is approximated from above by frozen continuous weighted controls.
Their trajectories converge, which suffices to pass every terminal inequality
to the limit. Combined with actual compactness of low-rank primitives this
proves attainment whenever the feasible set is nonempty.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped Topology

theorem terminalBound_tendsto_of_data
    (lamn Sn : ℕ → ℝ) {lam S z q : ℝ}
    (hlam : Tendsto lamn atTop (𝓝 lam)) (hS : Tendsto Sn atTop (𝓝 S))
    (hden : lam - q ≠ 0) :
    Tendsto (fun n => terminalBound (lamn n) (Sn n) z q) atTop
      (𝓝 (terminalBound lam S z q)) := by
  unfold terminalBound cap quadratic
  exact (tendsto_const_nhds.mul
    (((hlam.mul_const _).sub_const _).sub hS |>.sub
      (((((hlam.pow 2).sub (hlam.div_const 2)).add ((hlam.mul_const q).div_const 2))).sub
        ((hlam.mul hS).div_const (1-q))))).div (hlam.sub_const q) hden

/-- The terminal tests persist under the actual compactness topology: scalar
convergence and uniform convergence of primitives, without score convergence. -/
theorem passesTerminalTests_of_data_limit
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hpass : ∀ n, PassesTerminalTests (lamn n) (dn n) (continuation (lamn n) (dn n))) :
    PassesTerminalTests lam d (continuation lam d) := by
  intro z hz q hq
  have hz' : z ∈ Icc zStart zEnd :=
    ⟨(by norm_num [zStart, zTest] : zStart ≤ zTest).trans hz.1, hz.2⟩
  have hden : lam - q ≠ 0 := by
    have hl := hd.1.1
    have hqr := hq.2
    norm_num [lambdaLo, qHi] at hl hqr
    linarith
  have hT := terminalBound_tendsto_of_data lamn (fun n => (dn n).S) hlam hS hden (z := z)
  have hupper (eps : ℝ) (heps : 0 < eps) :
      terminalBound lam d.S z q ≤ continuation lam d z +
        gronwallBound 0 ((19 : ℝ) / 2) eps (z - zStart) := by
    obtain ⟨Z, hZ, hgap⟩ := hd.exists_tentApproximation hd.isContinuation heps
    choose Zn hZn using fun n => (hn n).exists_frozenTentTrajectory hd (continuation lam d)
      (continuation_continuous hd.isContinuation) heps
    have hlim := frozenTentTrajectory_tendstoUniformlyOn lamn dn hn hd hd hlam hS hJ
      (continuation lam d) (continuation_continuous hd.isContinuation) heps Zn Z hZn hZ
    have hTZ : terminalBound lam d.S z q ≤ Z z := by
      apply le_of_tendsto_of_tendsto' hT (hlim.tendsto_at hz')
      intro n
      exact (hpass n z hz q hq).trans
        ((hn n).frozenTentTrajectory_above hd (continuation lam d) heps
          (hn n).isContinuation (hZn n) z hz')
    exact hTZ.trans (hgap z hz').2
  have hc : ContinuousWithinAt
      (fun eps : ℝ => continuation lam d z + gronwallBound 0 ((19 : ℝ) / 2) eps (z-zStart))
      (Ioi 0) 0 :=
    (continuous_const.add (gronwallBound_continuous_ε 0 ((19 : ℝ) / 2) (z-zStart))).continuousWithinAt
  have hl := continuousWithinAt_const.closure_le
    (by simp only [closure_Ioi, self_mem_Ici] : (0 : ℝ) ∈ closure (Ioi (0 : ℝ))) hc hupper
  simpa only [gronwallBound_ε0_δ0, add_zero] using hl

/-- Feasibility is a closed property of the parameter. This uses compactness
of genuine admissible data, rather than assuming compactness of minimizers. -/
theorem feasible_parameters_isClosed : IsClosed {lam : ℝ | Feasible lam} := by
  apply IsSeqClosed.isClosed
  intro lamn lam hn hlam
  choose dn hd hp using fun n => (feasible_iff_canonical (lamn n)).mp (hn n)
  obtain ⟨lam', d, h, k, hk, hlam', hS, hJ⟩ := admissible_subsequence lamn dn hd
  have heq : lam' = lam := tendsto_nhds_unique hlam' (hlam.comp hk.tendsto_atTop)
  subst lam'
  apply (feasible_iff_canonical lam).mpr
  exact ⟨d, h, passesTerminalTests_of_data_limit
    (fun n => lamn (k n)) (fun n => dn (k n)) (fun n => hd (k n))
    h hlam' hS hJ (fun n => hp (k n))⟩

/-- The infimum in (4.5) is attained as soon as one feasible datum has been
constructed. The separate numerical upper witness discharges nonemptiness. -/
theorem lambdaStar_feasible (hne : ∃ lam, Feasible lam) : Feasible lambdaStar :=
  feasible_parameters_isClosed.csInf_mem hne feasible_parameters_bddBelow

theorem lambdaStar_admissible_minimizer (hne : ∃ lam, Feasible lam) :
    ∃ d, Admissible lambdaStar d ∧
      PassesTerminalTests lambdaStar d (continuation lambdaStar d) :=
  (feasible_iff_canonical lambdaStar).mp (lambdaStar_feasible hne)

end OptimalG.Variational
