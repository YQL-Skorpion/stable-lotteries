import OptimalG.VariationalNormLimit

/-! Norm continuity of the actual essential-infimum vector field. -/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

private theorem control_p_bounded : EssentiallyBounded (fun c : Control => c.1) controlMeasure := by
  refine ⟨1, ?_⟩
  filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
  have hp := hc.1
  norm_num [pLo, pHi] at hp
  exact abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩

private theorem control_x_bounded : EssentiallyBounded (fun c : Control => c.2.1) controlMeasure := by
  refine ⟨1, ?_⟩
  filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
  have hx := hc.2.1
  norm_num [xLo, xHi] at hx
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

private theorem control_y_bounded : EssentiallyBounded (fun c : Control => c.2.2) controlMeasure := by
  refine ⟨1, ?_⟩
  filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
  have hy := hc.2.2
  have hlo := (le_max_left xLo c.1).trans hy.1
  norm_num [xLo, xHi] at hy hlo
  exact abs_le.mpr ⟨by linarith, by linarith [hy.2]⟩

theorem Admissible.control_R_bounded {lam : ℝ} {d : LowRankData} (h : Admissible lam d) :
    EssentiallyBounded (fun c : Control => primitive lam d c.1) controlMeasure := by
  refine ⟨2, ?_⟩
  filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
  rw [abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 826 / 10000).trans (h.control_R_lower hc.1))]
  exact h.control_R_upper hc.1

/-- Uniform convergence of primitive maps controls all primitive evaluations in
the rational controls, including the cap branch below ell. -/
theorem control_primitive_AENormTendsto
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop) :
    BoundedAENormTendsto (fun n (c : Control) => primitive (lamn n) (dn n) c.1)
      (fun c : Control => primitive lam d c.1) controlMeasure := by
  have hl := BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure) hlam
  have hs := BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure) hS
  have hp := BoundedAENormTendsto.refl _ control_p_bounded
  have hden := (BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure)
    (tendsto_const_nhds (x := (1 : ℝ)))).sub hp
  have hdenbound : ∀ᵐ c ∂controlMeasure, (1 : ℝ) / 2 ≤ |1-c.1| := by
    filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
    have hpc := hc.1.2
    norm_num [pHi] at hpc
    have habs := le_abs_self (1-c.1)
    linarith
  have hcap : BoundedAENormTendsto (fun n (c : Control) => cap (lamn n) (dn n).S c.1)
      (fun c : Control => cap lam d.S c.1) controlMeasure :=
    ((hl.pow_two.sub (hl.div_const 2)).add ((hl.mul hp).div_const 2)).sub
      ((hl.mul hs).div hden (by norm_num : (0 : ℝ) < 1/2) (fun _ => hdenbound) hdenbound)
  have hjmap : Tendsto (fun n => lowPrimitiveMap (hn n)) atTop (𝓝 (lowPrimitiveMap hd)) :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hJ
  have hje : AENormTendsto
      (fun n (c : Control) => extendLowPrimitive (lowPrimitiveMap (hn n)) c.1)
      (fun c : Control => extendLowPrimitive (lowPrimitiveMap hd) c.1) controlMeasure := by
    refine ⟨fun n => dist (lowPrimitiveMap (hn n)) (lowPrimitiveMap hd), ?_, fun n => ⟨dist_nonneg, ?_⟩⟩
    · simpa only [dist_self] using hjmap.dist (tendsto_const_nhds (x := lowPrimitiveMap hd))
    · apply Eventually.of_forall
      intro c
      simpa only [extendLowPrimitive, Real.dist_eq] using
        BoundedContinuousFunction.dist_coe_le_dist
          (f := lowPrimitiveMap (hn n)) (g := lowPrimitiveMap hd)
          (projIcc ell tEnd (by norm_num [ell, tEnd]) c.1)
  have heq {L : ℝ} {D : LowRankData} (hD : Admissible L D) :
      (fun c : Control => if c.1 ≤ ell then cap L D.S c.1
        else extendLowPrimitive (lowPrimitiveMap hD) c.1) =ᵐ[controlMeasure]
      (fun c : Control => primitive L D c.1) := by
    filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
    by_cases hle : c.1 ≤ ell
    · simp only [hle, if_pos, primitive]
    · have hte : c.1 ≤ tEnd := hc.1.2.trans (by norm_num [pHi, tEnd])
      simp only [hle, if_neg, primitive, hte, if_pos]
      exact extendLowPrimitive_of_mem (lowPrimitiveMap hD) ⟨c.1, ⟨(lt_of_not_ge hle).le, hte⟩⟩
  exact ⟨(hcap.converges.ite hje (fun c => c.1 ≤ ell)).congr (fun n => heq (hn n)) (heq hd),
    hd.control_R_bounded⟩

/-- Strong convergence of the scores, unlike weak-* convergence alone, gives
norm convergence of every actual rational control at each time and state. -/
theorem controlH_AENormTendsto
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)))
    (z u : ℝ) :
    BoundedAENormTendsto (fun n => controlH (lamn n) (dn n) z u)
      (controlH lam d z u) controlMeasure := by
  have hl := BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure) hlam
  have hs := BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure) hS
  have const (v : ℝ) := BoundedAENormTendsto.scalar (I := Control) (μ := controlMeasure)
    (tendsto_const_nhds (x := v))
  have hp := BoundedAENormTendsto.refl _ control_p_bounded
  have hx := BoundedAENormTendsto.refl _ control_x_bounded
  have hy := BoundedAENormTendsto.refl _ control_y_bounded
  have hfx : BoundedAENormTendsto (fun n (c : Control) => (dn n).phi c.2.1)
      (fun c : Control => d.phi c.2.1) controlMeasure := by
    refine ⟨hphi.comp (fun c => c.2.1) (fun P hP => (ae_control_lowRanks P hP).mono fun _ h => h.1), ?_⟩
    refine ⟨1/3, ?_⟩
    simpa only [Real.norm_eq_abs] using (ae_control_lowRanks _ hd.phi_norm_bound).mono (fun _ h => h.1)
  have hfy : BoundedAENormTendsto (fun n (c : Control) => (dn n).phi c.2.2)
      (fun c : Control => d.phi c.2.2) controlMeasure := by
    refine ⟨hphi.comp (fun c => c.2.2) (fun P hP => (ae_control_lowRanks P hP).mono fun _ h => h.2), ?_⟩
    refine ⟨1/3, ?_⟩
    simpa only [Real.norm_eq_abs] using (ae_control_lowRanks _ hd.phi_norm_bound).mono (fun _ h => h.2)
  have hR := control_primitive_AENormTendsto lamn dn hn hd hlam hS hJ
  have hP := ((hl.mul ((const 1).sub hp)).sub (((const 1).sub hp).pow_two.div_const 2)).sub hs
  have hK := (((hl.mul ((const z).sub hp)).sub (((const z).sub hp).pow_two.div_const 2)).sub hs).sub (const u)
  have hh := (hl.const_mul 2).sub hx
  have hk := (hp.add hy).sub hl
  have hD := (hh.mul hR).sub (hk.mul hP)
  have hnum := (((const z).sub hl).mul ((hR.mul hfx).add (hP.mul hfy))).add
    (hK.mul ((hk.mul hfx).add (hh.mul hfy)))
  have hb {L : ℝ} {D : LowRankData} (h : Admissible L D) :
      ∀ᵐ c ∂controlMeasure, (3 : ℝ) / 100 ≤ |controlDeterminant L D c| := by
    filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
    exact (h.determinant_positive hc).le.trans (le_abs_self _)
  exact hnum.neg.div hD (by norm_num : (0 : ℝ) < 3/100) (fun n => hb (hn n)) (hb hd)

theorem vectorField_tendsto_of_strong_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)))
    (z u : ℝ) :
    Tendsto (fun n => vectorField (lamn n) (dn n) z u) atTop (𝓝 (vectorField lam d z u)) :=
  (hlam.sub_const z).min ((controlH_AENormTendsto lamn dn hn hd hlam hS hJ hphi z u).converges.essInf_tendsto
    (fun n => (hn n).controlH_bounded z u) (hd.controlH_bounded z u))

end OptimalG.Variational
