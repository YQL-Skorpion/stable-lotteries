import OptimalG.VariationalAttainment
import OptimalG.VariationalStrictLimit
import OptimalG.VariationalNormPrimitive
import OptimalG.SlaterPerturbation

/-!
# Strict-trial perturbation and active terminal tests

Convex mixing with the explicit Slater datum creates strict low-rank margins.
Norm continuity then permits a smaller parameter while retaining the terminal
inequalities. Consequently an interior minimum has an actual terminal contact.
-/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

theorem mixData_scores_AENormTendsto {lam : ℝ} {d e : LowRankData}
    (hd : Admissible lam d) (he : Admissible lam e) {tn : ℕ → ℝ}
    (ht : Tendsto tn atTop (𝓝 0)) :
    AENormTendsto (fun n => (mixData (tn n) d e).phi) d.phi (volume.restrict (Icc ell tEnd)) := by
  have hbD : EssentiallyBounded d.phi (volume.restrict (Icc ell tEnd)) :=
    ⟨1/3, by simpa only [Real.norm_eq_abs] using hd.phi_norm_bound⟩
  have hbE : EssentiallyBounded e.phi (volume.restrict (Icc ell tEnd)) :=
    ⟨1/3, by simpa only [Real.norm_eq_abs] using he.phi_norm_bound⟩
  have ht' := BoundedAENormTendsto.scalar (I := ℝ) (μ := volume.restrict (Icc ell tEnd)) ht
  have h1 := BoundedAENormTendsto.scalar (I := ℝ) (μ := volume.restrict (Icc ell tEnd))
    (tendsto_const_nhds (x := (1 : ℝ)))
  have hc := ((h1.sub ht').mul (BoundedAENormTendsto.refl _ hbD)).add
    (ht'.mul (BoundedAENormTendsto.refl _ hbE))
  simpa only [sub_zero, one_mul, zero_mul, add_zero, mixData] using hc.converges

theorem lambdaShift_scores_AENormTendsto {lam : ℝ} {d : LowRankData} {lamn : ℕ → ℝ}
    (hlam : Tendsto lamn atTop (𝓝 lam)) :
    AENormTendsto (fun n => (lambdaShiftData lam (lamn n) d).phi) d.phi
      (volume.restrict (Icc ell tEnd)) := by
  have hk : Tendsto (fun n => lambdaShiftConstant lam (lamn n) d.S) atTop (𝓝 0) := by
    have hh := (lambdaShiftConstant_continuous lam d.S).continuousAt.tendsto.comp hlam
    change Tendsto (fun n => lambdaShiftConstant lam (lamn n) d.S) atTop
      (𝓝 (lambdaShiftConstant lam lam d.S)) at hh
    simpa only [lambdaShiftConstant_self] using hh
  simpa only [lambdaShiftData, add_zero] using
    (AENormTendsto.refl (μ := volume.restrict (Icc ell tEnd)) d.phi).add
      (AENormTendsto.of_scalar hk)

/-- A strict low-rank datum with a strict terminal margin admits a smaller
feasible parameter whenever the current parameter is above the lower endpoint. -/
theorem exists_lower_feasible_of_strict_margins {lam eps δ : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hm : StrictLowMargins lam d eps) (heps : 0 < eps) (hδ : 0 < δ)
    (hmargin : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q + δ ≤ continuation lam d z) :
    ∃ lam' < lam, Feasible lam' := by
  obtain ⟨ln, _, hln, ht⟩ := exists_seq_strictMono_tendsto' hl
  have had : ∀ᶠ n in atTop, Admissible (ln n) (lambdaShiftData lam (ln n) d) := by
    filter_upwards [ht.eventually (lambdaShift_admissible_eventually hd hm heps)] with n hn
    exact hn ⟨(hln n).1.le, (hln n).2.le.trans hd.1.2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp had
  let ln' : ℕ → ℝ := fun n => ln (n+N)
  let dn : ℕ → LowRankData := fun n => lambdaShiftData lam (ln' n) d
  have hn (n : ℕ) : Admissible (ln' n) (dn n) := hN (n+N) (Nat.le_add_left N n)
  have hlt : Tendsto ln' atTop (𝓝 lam) := ht.comp (tendsto_add_atTop_nat N)
  have hSt : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S) := tendsto_const_nhds
  have hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)) :=
    lambdaShift_scores_AENormTendsto hlt
  have hJ := lowPrimitive_tendstoUniformly_of_strong_data ln' dn hn hd hlt hSt hphi
  have hp := passesTerminalTests_eventually_of_strong_data ln' dn hn hd hlt hSt hJ hphi hδ hmargin
  obtain ⟨n, hpn⟩ := hp.exists
  refine ⟨ln' n, (hln (n+N)).2, (feasible_iff_canonical (ln' n)).mpr ⟨dn n, hn n, ?_⟩⟩
  intro z hz q hq
  have hh := hpn z hz q hq
  linarith

/-- Every strict terminal margin can first be combined with the checked Slater
trial, so no strict low-rank assumptions are needed in the resulting theorem. -/
theorem exists_lower_feasible_of_strict_terminal {lam δ : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam) (hδ : 0 < δ)
    (hmargin : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q + δ ≤ continuation lam d z) :
    ∃ lam' < lam, Feasible lam' := by
  obtain ⟨tn, _, htn, ht⟩ := exists_seq_strictAnti_tendsto' (by norm_num : (0 : ℝ) < 1)
  let dn := fun n => mixData (tn n) d (slaterData lam)
  have hm (n : ℕ) := mixed_slater_strict hd ⟨(htn n).1.le, (htn n).2.le⟩
  have hn (n : ℕ) : Admissible lam (dn n) := (hm n).1
  have hSt : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S) := by
    dsimp [dn, mixData]
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul_const d.S).add
      (ht.mul_const (slaterData lam).S)
  have hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)) :=
    mixData_scores_AENormTendsto hd (slater_admissible lam hd.1) ht
  have hJ := lowPrimitive_tendstoUniformly_of_strong_data (fun _ => lam) dn hn hd
    tendsto_const_nhds hSt hphi
  have hp := passesTerminalTests_eventually_of_strong_data (fun _ => lam) dn hn hd
    tendsto_const_nhds hSt hJ hphi hδ hmargin
  obtain ⟨n, hpn⟩ := hp.exists
  exact exists_lower_feasible_of_strict_margins (hn n) hl (hm n).2
    (div_pos (htn n).1 (by norm_num)) (div_pos hδ (by norm_num)) hpn

/-- An interior variational minimizer has no uniform strict terminal margin. -/
theorem minimizer_no_strict_terminal_margin {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam') :
    ¬ ∃ δ > 0, ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q + δ ≤ continuation lam d z := by
  rintro ⟨δ, hδ, hm⟩
  obtain ⟨lam', hlt, hf⟩ := exists_lower_feasible_of_strict_terminal hd hl hδ hm
  exact (not_lt_of_ge (hmin lam' hf)) hlt

theorem lambdaStar_terminal_contact {d : LowRankData}
    (hd : Admissible lambdaStar d) (hl : lambdaLo < lambdaStar)
    (hp : PassesTerminalTests lambdaStar d (continuation lambdaStar d)) :
    ∃ z ∈ Icc zTest zEnd, ∃ q ∈ Icc qLo qHi,
      terminalBound lambdaStar d.S z q = continuation lambdaStar d z :=
  terminal_contact_of_no_strict_margin hd hp
    (minimizer_no_strict_terminal_margin hd hl fun _ h => lambdaStar_le_feasible h)

end OptimalG.Variational
