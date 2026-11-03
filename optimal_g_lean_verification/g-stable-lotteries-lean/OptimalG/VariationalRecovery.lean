import OptimalG.VariationalCompactness
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Recovering a measurable score from a primitive

Uniform primitive limits suffice for compactness: the derivative of the limit
recovers the score, and the fundamental theorem for absolutely continuous
functions restores the defining integral identity.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

theorem quadratic_hasDerivAt (lam r : ℝ) :
    HasDerivAt (quadratic lam) (lam - r) r := by
  have hi : HasDerivAt (fun r : ℝ => r) 1 r := hasDerivAt_id r
  have hh := (hi.const_mul lam).sub ((hi.pow 2).div_const 2)
  have hs : lam * 1 - ((↑(2 : ℕ) : ℝ) * r ^ (2 - 1) * 1) / 2 = lam - r := by norm_num
  rw [hs] at hh
  exact hh

theorem primitive_deriv_bounds (lam : ℝ) (J : ℝ → ℝ)
    (hlam : lam ∈ Icc lambdaLo lambdaHi)
    (hm : MonotoneOn J (Icc ell tEnd))
    (hs : MonotoneOn (fun r => quadratic lam r - J r) (Icc ell tEnd)) :
    ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ deriv J r ∧ deriv J r ≤ lam - r := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  apply Eventually.of_forall
  intro r hr
  have hnhds : Icc ell tEnd ∈ 𝓝 r := Icc_mem_nhds hr.1 hr.2
  have hnonneg := hm.derivWithin_nonneg (x := r)
  rw [derivWithin_of_mem_nhds hnhds] at hnonneg
  refine ⟨hnonneg, ?_⟩
  by_cases hd : DifferentiableAt ℝ J r
  · have hslack := hs.derivWithin_nonneg (x := r)
    rw [derivWithin_of_mem_nhds hnhds] at hslack
    change 0 ≤ deriv (quadratic lam - J) r at hslack
    rw [((quadratic_hasDerivAt lam r).sub hd.hasDerivAt).deriv] at hslack
    linarith
  · rw [deriv_zero_of_not_differentiableAt hd]
    have hlo := hlam.1
    have hrhi := hr.2
    norm_num [lambdaLo, tEnd] at hlo hrhi
    linarith

/-- Exact recovery of an admissible low-rank score from its Lipschitz primitive.
All inequalities in the hypotheses are closed under uniform convergence. -/
theorem admissible_of_primitive (lam S : ℝ) (J : ℝ → ℝ)
    (hlam : lam ∈ Icc lambdaLo lambdaHi) (hS : S ≤ slackUpper lam)
    (hLip : LipschitzOnWith (1 / 3 : ℝ≥0) J (Icc ell tEnd))
    (hleft : J ell = cap lam S ell) (hright : J tEnd = quadratic lam tEnd - S)
    (hcap : ∀ r ∈ Icc ell tEnd, J r ≤ cap lam S r)
    (hm : MonotoneOn J (Icc ell tEnd))
    (hs : MonotoneOn (fun r => quadratic lam r - J r) (Icc ell tEnd)) :
    Admissible lam ⟨S, deriv J⟩ ∧
      ∀ r ∈ Icc ell tEnd, lowPrimitive lam ⟨S, deriv J⟩ r = J r := by
  have hnorm : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), ‖deriv J r‖ ≤ (1 : ℝ) / 3 := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    apply (ae_restrict_iff' measurableSet_Ioo).mpr
    apply Eventually.of_forall
    intro r hr
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr.1 hr.2) hLip
  have hLp : MemLp (deriv J) ⊤ (volume.restrict (Icc ell tEnd)) :=
    memLp_top_of_bound (stronglyMeasurable_deriv J).aestronglyMeasurable (1 / 3) hnorm
  have hrecover : ∀ r ∈ Icc ell tEnd, lowPrimitive lam ⟨S, deriv J⟩ r = J r := by
    intro r hr
    have hi : LipschitzOnWith (1 / 3 : ℝ≥0) J (uIcc ell r) := by
      rw [uIcc_of_le hr.1]
      exact hLip.mono (fun _ hu => ⟨hu.1, hu.2.trans hr.2⟩)
    have hFTC := hi.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    dsimp [lowPrimitive]
    rw [hFTC, hleft]
    ring
  refine ⟨⟨hlam, hS, hLp, primitive_deriv_bounds lam J hlam hm hs, ?_, ?_⟩, hrecover⟩
  · rw [hrecover tEnd (by norm_num [ell, tEnd])]
    exact hright
  · intro r hr
    rw [hrecover r hr]
    exact hcap r hr

/-- Extend a primitive on the compact interval by clamping its argument. -/
noncomputable def extendLowPrimitive (J : LowRankInterval →ᵇ ℝ) : ℝ → ℝ :=
  fun r => J (projIcc ell tEnd (by norm_num [ell, tEnd]) r)

theorem extendLowPrimitive_of_mem (J : LowRankInterval →ᵇ ℝ) (r : LowRankInterval) :
    extendLowPrimitive J r = J r := by
  simp [extendLowPrimitive, projIcc_of_mem]

theorem extendLowPrimitive_lipschitz (J : LowRankInterval →ᵇ ℝ)
    (hJ : LipschitzWith (1 / 3 : ℝ≥0) J) :
    LipschitzWith (1 / 3 : ℝ≥0) (extendLowPrimitive J) := by
  change LipschitzWith (1 / 3 : ℝ≥0)
    (J ∘ projIcc ell tEnd (show ell ≤ tEnd by norm_num [ell, tEnd]))
  simpa only [mul_one] using hJ.comp (LipschitzWith.projIcc
    (show ell ≤ tEnd by norm_num [ell, tEnd]))

/-- Passing to limits of the scalar parameters and uniformly convergent
primitives preserves every low-rank admissibility condition. -/
theorem admissible_of_primitive_limit
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData)
    (hn : ∀ n, Admissible (lamn n) (dn n))
    (lam S : ℝ) (J : LowRankInterval →ᵇ ℝ)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) J atTop)
    (hLip : LipschitzWith (1 / 3 : ℝ≥0) J) :
    Admissible lam ⟨S, deriv (extendLowPrimitive J)⟩ ∧
      ∀ r ∈ Icc ell tEnd,
        lowPrimitive lam ⟨S, deriv (extendLowPrimitive J)⟩ r = extendLowPrimitive J r := by
  have hpoint (r : ℝ) (hr : r ∈ Icc ell tEnd) :
      Tendsto (fun n => lowPrimitive (lamn n) (dn n) r) atTop (𝓝 (extendLowPrimitive J r)) := by
    have he := extendLowPrimitive_of_mem J ⟨r, hr⟩
    change extendLowPrimitive J r = J ⟨r, hr⟩ at he
    rw [he]
    exact hJ.tendsto_at ⟨r, hr⟩
  have hquad (r : ℝ) : Tendsto (fun n => quadratic (lamn n) r) atTop (𝓝 (quadratic lam r)) := by
    exact (hlam.mul_const r).sub tendsto_const_nhds
  have hcaplim (r : ℝ) : Tendsto (fun n => cap (lamn n) (dn n).S r)
      atTop (𝓝 (cap lam S r)) := by
    exact (((hlam.pow 2).sub (hlam.div_const 2)).add
      ((hlam.mul_const r).div_const 2)).sub ((hlam.mul hS).div_const (1 - r))
  have hlamRange : lam ∈ Icc lambdaLo lambdaHi :=
    isClosed_Icc.mem_of_tendsto hlam (Eventually.of_forall (fun n => (hn n).1))
  have hSupper : S ≤ slackUpper lam := by
    have hu : Tendsto (fun n => slackUpper (lamn n)) atTop (𝓝 (slackUpper lam)) :=
      tendsto_const_nhds.sub ((tendsto_const_nhds.sub hlam).div_const 2)
    exact le_of_tendsto_of_tendsto hS hu (Eventually.of_forall (fun n => (hn n).2.1))
  apply admissible_of_primitive lam S (extendLowPrimitive J) hlamRange hSupper
    (extendLowPrimitive_lipschitz J hLip).lipschitzOnWith
  · have hi := hpoint ell (by norm_num [ell, tEnd])
    have hc := hcaplim ell
    simp only [lowPrimitive_at_ell] at hi
    exact tendsto_nhds_unique hi hc
  · have hi := hpoint tEnd (by norm_num [ell, tEnd])
    have hc := (hquad tEnd).sub hS
    have hid : (fun n => lowPrimitive (lamn n) (dn n) tEnd) =
        (fun n => quadratic (lamn n) tEnd - (dn n).S) :=
      funext (fun n => (hn n).2.2.2.2.1)
    rw [hid] at hi
    exact tendsto_nhds_unique hi hc
  · intro r hr
    exact le_of_tendsto_of_tendsto (hpoint r hr) (hcaplim r)
      (Eventually.of_forall (fun n => (hn n).lowPrimitive_le_cap hr))
  · intro a ha b hb hab
    exact le_of_tendsto_of_tendsto (hpoint a ha) (hpoint b hb)
      (Eventually.of_forall (fun n => (hn n).lowPrimitive_monotone.1 ha hb hab))
  · intro a ha b hb hab
    exact le_of_tendsto_of_tendsto ((hquad a).sub (hpoint a ha)) ((hquad b).sub (hpoint b hb))
      (Eventually.of_forall (fun n => (hn n).lowPrimitive_monotone.2 ha hb hab))

/-- Sequential compactness of the admissible sets when viewed through scalar
parameters and primitives. The limiting score is an actual essentially bounded
measurable derivative, not an abstract weak-star functional. -/
theorem admissible_subsequence
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData)
    (hn : ∀ n, Admissible (lamn n) (dn n)) :
    ∃ lam : ℝ, ∃ d : LowRankData, ∃ hd : Admissible lam d, ∃ k : ℕ → ℕ,
      StrictMono k ∧ Tendsto (fun n => lamn (k n)) atTop (𝓝 lam) ∧
      Tendsto (fun n => (dn (k n)).S) atTop (𝓝 d.S) ∧
      TendstoUniformly (fun n => lowPrimitiveMap (hn (k n))) (lowPrimitiveMap hd) atTop := by
  let v : ℕ → ℝ × ℝ := fun n => (lamn n, (dn n).S)
  have hv (n : ℕ) : v n ∈ (Icc lambdaLo lambdaHi ×ˢ
      Icc ((21972 : ℝ) / 1000000) ((26651 : ℝ) / 1000000)) :=
    ⟨(hn n).1, (hn n).slack_lower, (hn n).slack_upper⟩
  obtain ⟨vlim, _, k1, hk1, hvlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hv
  obtain ⟨J, k2, hk2, hJ, hLip, _⟩ := admissible_primitives_subsequence
    (fun n => lamn (k1 n)) (fun n => dn (k1 n)) (fun n => hn (k1 n))
  let k : ℕ → ℕ := k1 ∘ k2
  have hlam : Tendsto (fun n => lamn (k n)) atTop (𝓝 vlim.1) :=
    (continuous_fst.tendsto vlim).comp (hvlim.comp hk2.tendsto_atTop)
  have hS : Tendsto (fun n => (dn (k n)).S) atTop (𝓝 vlim.2) :=
    (continuous_snd.tendsto vlim).comp (hvlim.comp hk2.tendsto_atTop)
  obtain ⟨hd, hrecover⟩ := admissible_of_primitive_limit
    (fun n => lamn (k n)) (fun n => dn (k n)) (fun n => hn (k n))
    vlim.1 vlim.2 J hlam hS hJ hLip
  have hmap : lowPrimitiveMap hd = J := by
    ext r
    change lowPrimitive vlim.1 ⟨vlim.2, deriv (extendLowPrimitive J)⟩ r = J r
    rw [hrecover r r.property, extendLowPrimitive_of_mem]
  refine ⟨vlim.1, ⟨vlim.2, deriv (extendLowPrimitive J)⟩, hd, k, hk1.comp hk2,
    hlam, hS, ?_⟩
  rwa [hmap]

end OptimalG.Variational
