import OptimalG.VariationalStrongFlow
import OptimalG.TerminalContact

/-! Uniform strict terminal margins persist under strong admissible perturbations. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

private def terminalParameterBox : Set (ℝ × ℝ) := Icc lambdaLo lambdaHi ×ˢ Icc 0 1

private theorem terminal_parameter_mem {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    (lam, d.S) ∈ terminalParameterBox := by
  refine ⟨hd.1, ?_, ?_⟩
  · have hh := hd.slack_lower; linarith
  · have hh := hd.slack_upper; linarith

private theorem terminalBound_parameter_continuous :
    ContinuousOn (fun v : (ℝ × ℝ) × (ℝ × ℝ) => terminalBound v.1.1 v.1.2 v.2.1 v.2.2)
      (terminalParameterBox ×ˢ terminalDomain) := by
  unfold terminalBound cap quadratic
  apply ContinuousOn.div
  · apply ContinuousOn.mul (by fun_prop)
    apply ContinuousOn.sub
    · fun_prop
    · apply ContinuousOn.sub
      · fun_prop
      · apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro v hv
        have hh := hv.2.2.2
        dsimp [qHi] at hh
        linarith
  · fun_prop
  · intro v hv
    have hl := hv.1.1.1
    have hh := hv.2.2.2
    dsimp [lambdaLo] at hl
    dsimp [qHi] at hh
    linarith

theorem terminalBound_tendstoUniformlyOn_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S)) :
    TendstoUniformlyOn (fun n (v : ℝ × ℝ) => terminalBound (lamn n) (dn n).S v.1 v.2)
      (fun v : ℝ × ℝ => terminalBound lam d.S v.1 v.2) atTop terminalDomain := by
  have hc : IsCompact (terminalParameterBox ×ˢ terminalDomain) :=
    (isCompact_Icc.prod isCompact_Icc).prod terminalDomain_compact
  have hu := hc.uniformContinuousOn_of_continuous terminalBound_parameter_continuous
  have ht : TendstoUniformlyOn
      (fun a v : ℝ × ℝ => terminalBound a.1 a.2 v.1 v.2)
      (fun v : ℝ × ℝ => terminalBound lam d.S v.1 v.2)
      (𝓝[terminalParameterBox] (lam, d.S)) terminalDomain :=
    hu.tendstoUniformlyOn (terminal_parameter_mem hd)
  have hdata : Tendsto (fun n => (lamn n, (dn n).S)) atTop
      (𝓝[terminalParameterBox] (lam, d.S)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlam.prodMk_nhds hS,
      Eventually.of_forall fun n => terminal_parameter_mem (hn n)⟩
  rw [Metric.tendstoUniformlyOn_iff] at ht ⊢
  intro eps heps
  exact hdata.eventually (ht eps heps)

/-- In particular, a strict terminal margin is an open condition in the strong
admissible-data topology. -/
theorem passesTerminalTests_eventually_of_strong_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)))
    {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound lam d.S z q + δ ≤ continuation lam d z) :
    ∀ᶠ n in atTop, ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      terminalBound (lamn n) (dn n).S z q + δ/3 ≤ continuation (lamn n) (dn n) z := by
  have hT := terminalBound_tendstoUniformlyOn_of_data lamn dn hn hd hlam hS
  have hY := continuation_tendstoUniformlyOn_of_strong_data lamn dn hn hd hlam hS hJ hphi
  rw [Metric.tendstoUniformlyOn_iff] at hT hY
  have heps : 0 < δ/3 := by positivity
  filter_upwards [hT (δ/3) heps, hY (δ/3) heps] with n hTn hYn
  intro z hz q hq
  have hz' : z ∈ Icc zStart zEnd :=
    ⟨(by norm_num [zStart, zTest] : zStart ≤ zTest).trans hz.1, hz.2⟩
  have htc := hTn (z,q) ⟨hz,hq⟩
  have hyc := hYn z hz'
  rw [Real.dist_eq] at htc hyc
  have hm := hmargin z hz q hq
  dsimp at htc
  linarith [(abs_lt.mp htc).1, (abs_lt.mp htc).2, (abs_lt.mp hyc).1, (abs_lt.mp hyc).2]

end OptimalG.Variational
