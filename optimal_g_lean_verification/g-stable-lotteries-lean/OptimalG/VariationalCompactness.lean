import OptimalG.VariationalBounds
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Compactness through low-rank primitives

The low-rank primitives have a common Lipschitz constant. Uniform limits retain
both increment inequalities; their almost-everywhere derivatives consequently
recover the measurable scores. This is the primitive formulation of the
weak-star compactness step in B.2.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

theorem Admissible.lowPrimitive_sub {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {a b : ℝ}
    (ha : a ∈ Icc ell tEnd) (hb : b ∈ Icc ell tEnd) :
    lowPrimitive lam d b - lowPrimitive lam d a = ∫ r in a..b, d.phi r := by
  unfold lowPrimitive
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (h.intervalIntegrable le_rfl hb.1 hb.2) (h.intervalIntegrable le_rfl ha.1 ha.2)

/-- The two integrated slope constraints used in passing to a uniform limit. -/
theorem Admissible.lowPrimitive_increment {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {a b : ℝ}
    (ha : a ∈ Icc ell tEnd) (hb : b ∈ Icc ell tEnd) (hab : a ≤ b) :
    0 ≤ lowPrimitive lam d b - lowPrimitive lam d a ∧
      lowPrimitive lam d b - lowPrimitive lam d a ≤ quadratic lam b - quadratic lam a := by
  rw [h.lowPrimitive_sub ha hb]
  have hbounds : ∀ᵐ r ∂volume.restrict (Icc a b), 0 ≤ d.phi r ∧ d.phi r ≤ lam - r := by
    apply ae_restrict_of_ae_restrict_of_subset ?_ h.2.2.2.1
    intro r hr
    exact ⟨ha.1.trans hr.1, hr.2.trans hb.2⟩
  refine ⟨intervalIntegral.integral_nonneg_of_ae_restrict hab
    (hbounds.mono (fun _ hr => hr.1)), ?_⟩
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (h.intervalIntegrable ha.1 hab hb.2)
    ((continuous_const.sub continuous_id).intervalIntegrable a b)
    (hbounds.mono (fun _ hr => hr.2))
  change (∫ r in a..b, d.phi r) ≤ ∫ r in a..b, lam - r at hi
  rwa [integral_line] at hi

theorem Admissible.lowPrimitive_lipschitz {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    LipschitzOnWith (1 / 3 : ℝ≥0) (lowPrimitive lam d) (Icc ell tEnd) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [Real.dist_eq, ← neg_sub (lowPrimitive lam d b) (lowPrimitive lam d a), abs_neg,
    h.lowPrimitive_sub ha hb]
  have hglobal := (ae_restrict_iff' measurableSet_Icc).mp h.2.2.2.1
  have hnorm : ∀ᵐ r, r ∈ uIoc a b → ‖d.phi r‖ ≤ (1 : ℝ) / 3 := by
    filter_upwards [hglobal] with r hr hri
    have hrell : ell ≤ r := (le_min ha.1 hb.1).trans hri.1.le
    have hrend : r ≤ tEnd := hri.2.trans (max_le ha.2 hb.2)
    have hphi := hr ⟨hrell, hrend⟩
    have hlam := h.1.2
    norm_num [lambdaHi, ell] at hlam hrell
    rw [Real.norm_eq_abs, abs_of_nonneg hphi.1]
    linarith [hphi.2]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae hnorm
  simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hi

/-- Both the primitive and its slack relative to the parabola are monotone. -/
theorem Admissible.lowPrimitive_monotone {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) :
    MonotoneOn (lowPrimitive lam d) (Icc ell tEnd) ∧
    MonotoneOn (fun r => quadratic lam r - lowPrimitive lam d r) (Icc ell tEnd) := by
  constructor
  · intro a ha b hb hab
    linarith [(h.lowPrimitive_increment ha hb hab).1]
  · intro a ha b hb hab
    linarith [(h.lowPrimitive_increment ha hb hab).2]

theorem Admissible.lowPrimitive_range {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam d r ∈ Icc 0 3 := by
  have he : ell ∈ Icc pLo pHi := by norm_num [ell, pLo, pHi]
  have he' : ell ∈ Icc ell tEnd := by norm_num [ell, tEnd]
  have hlow := h.control_R_lower he
  have hupp := h.control_R_upper he
  rw [primitive_at_ell, ← lowPrimitive_at_ell] at hlow hupp
  have hmono := h.lowPrimitive_monotone.1 he' hr hr.1
  have hlip := h.lowPrimitive_lipschitz.dist_le_mul r hr ell he'
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hmono),
    abs_of_nonneg (sub_nonneg.mpr hr.1)] at hlip
  norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hlip
  have hrhi := hr.2
  norm_num [tEnd, ell] at hrhi hlip hupp
  exact ⟨by linarith, by linarith⟩

abbrev LowRankInterval := Icc ell tEnd

noncomputable def lowPrimitiveMap {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) : LowRankInterval →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun r : LowRankInterval => lowPrimitive lam d r,
      h.lowPrimitive_lipschitz.to_restrict.continuous⟩

/-- Every sequence of admissible primitives admits a uniformly convergent
subsequence. The limit retains the common Lipschitz constant. No weak topology
or pre-existing optimizer is assumed. -/
theorem admissible_primitives_subsequence
    (lam : ℕ → ℝ) (d : ℕ → LowRankData) (h : ∀ n, Admissible (lam n) (d n)) :
    ∃ J : LowRankInterval →ᵇ ℝ, ∃ k : ℕ → ℕ, StrictMono k ∧
      TendstoUniformly (fun n => lowPrimitiveMap (h (k n))) J atTop ∧
      LipschitzWith (1 / 3 : ℝ≥0) J ∧ ∀ r, J r ∈ Icc 0 3 := by
  let F : ℕ → LowRankInterval →ᵇ ℝ := fun n => lowPrimitiveMap (h n)
  have hF (n : ℕ) : LipschitzWith (1 / 3 : ℝ≥0) (F n) :=
    (h n).lowPrimitive_lipschitz.to_restrict
  have hequi : Equicontinuous ((↑) : range F → LowRankInterval → ℝ) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (1 : ℝ) / 3 * r)
      (by simpa using (tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun r : ℝ => (1 : ℝ) / 3 * r) (𝓝 0) (𝓝 ((1 : ℝ) / 3 * 0))))
    intro a b f
    obtain ⟨n, hn⟩ := f.property
    have hf := (hF n).dist_le_mul a b
    simpa only [hn, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hf
  have hcompact : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) 3) isCompact_Icc (range F)
      (by
        intro f r hf
        obtain ⟨n, rfl⟩ := hf
        exact (h n).lowPrimitive_range r.property) hequi
  obtain ⟨J, _, k, hk, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have heval (r : LowRankInterval) : Tendsto (fun n => F (k n) r) atTop (𝓝 (J r)) :=
    ((continuous_eval_const r).tendsto J).comp hconv
  refine ⟨J, k, hk, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro r s
    apply le_of_tendsto ((heval r).dist (heval s))
    exact Eventually.of_forall (fun n => (hF (k n)).dist_le_mul r s)
  · intro r
    constructor
    · apply ge_of_tendsto (heval r)
      exact Eventually.of_forall (fun n => ((h (k n)).lowPrimitive_range r.property).1)
    · apply le_of_tendsto (heval r)
      exact Eventually.of_forall (fun n => ((h (k n)).lowPrimitive_range r.property).2)

end OptimalG.Variational
