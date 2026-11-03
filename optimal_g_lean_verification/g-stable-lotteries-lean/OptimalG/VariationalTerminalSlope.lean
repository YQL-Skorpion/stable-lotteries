import OptimalG.VariationalCompletedConcavity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A smooth control touching the concave minimum at the terminal point
bounds all left chords. No derivative of the minimum itself is assumed. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

 theorem concave_chord_ge_touching_derivative {a b m : ℝ} {f g : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc a b) f)
    (hfg : ∀ r ∈ Icc a b,f r ≤ g r) (hjoin : f b=g b)
    (hg : HasDerivAt g m b) :
    ∀ r ∈ Ico a b,m*(b-r) ≤ f b-f r := by
  intro r hr
  have hm : m ≤ slope f b r := by
    apply le_of_tendsto (hg.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hr.2)] with t ht hrt
    have htab : t ∈ Icc a b := ⟨hr.1.trans hrt.le,ht.le⟩
    have hcomp : slope g b t ≤ slope f b t := by
      rw [slope_comm g b t,slope_comm f b t,slope_def_field,slope_def_field]
      apply (div_le_div_iff_of_pos_right (sub_pos.mpr ht)).mpr
      rw [← hjoin]
      linarith [hfg t htab]
    exact hcomp.trans (hf.antitoneOn_slope_lt ⟨hr.1.trans hr.2.le,le_rfl⟩
      ⟨⟨hr.1,hr.2.le⟩,hr.2⟩ ⟨htab,ht⟩ hrt.le)
  rw [slope_comm f b r,slope_def_field] at hm
  exact (le_div_iff₀ (sub_pos.mpr hr.2)).mp hm

 theorem highAffineControl_hasDerivAt {lam S p theta alpha b h : ℝ} {Y : ℝ → ℝ}
    (hY : HasDerivAt Y h b) :
    HasDerivAt (highAffineControl lam S p theta alpha Y)
      (-theta+alpha*(b-lam-p+h)) b := by
  have hq := ((quadratic_hasDerivAt lam (b-p)).comp b ((hasDerivAt_id b).sub_const p))
  have hh := (((hasDerivAt_id b).sub_const lam).const_mul (-theta)).sub
    (((hq.sub_const S).sub hY).const_mul alpha)
  convert! hh using 1 <;> (try simp only [highAffineControl,id_eq]) <;> ring

 theorem terminal_active_control_chord {lam b m : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y) (hb : b ∈ Ioo zStart zEnd)
    (hconcave : ConcaveOn ℝ (Icc zStart b) (continuationScore lam d Y))
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd b (Y b) v=vectorField lam d b (Y b))
    (hscalar : m ≤ -featureTheta lam d v+
      featureAlpha lam d v*(b-lam-v.1.1+continuationScore lam d Y b)) :
    ∀ r ∈ Ico zStart b,m*(b-r) ≤ continuationScore lam d Y b-continuationScore lam d Y r := by
  have hder := highAffineControl_hasDerivAt (lam:=lam) (S:=d.S) (p:=v.1.1)
    (theta:=featureTheta lam d v) (alpha:=featureAlpha lam d v)
    ((hY.2 b ⟨hb.1.le,hb.2.le⟩).hasDerivAt (Icc_mem_nhds hb.1 hb.2))
  have hh := concave_chord_ge_touching_derivative
    (g:=highAffineControl lam d.S v.1.1 (featureTheta lam d v) (featureAlpha lam d v) Y)
    hconcave (fun r hr => by
    rw [← featureH_as_highAffineControl hd hv]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH r (Y r) hv))
    (by rw [← featureH_as_highAffineControl hd hv];exact hactive.symm) hder
  intro r hr
  exact (mul_le_mul_of_nonneg_right hscalar (sub_nonneg.mpr hr.2.le)).trans (hh r hr)


 theorem terminal_chord_of_active_slope_bound {lam b m : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y) (hb : b ∈ Ioo zStart zEnd)
    (hconcave : ConcaveOn ℝ (Icc zStart b) (continuationScore lam d Y))
    (hm : m ≤ -1)
    (hscalar : ∀ v ∈ controlFeatureSupport d,
      featureH hd b (Y b) v=vectorField lam d b (Y b) →
      vectorField lam d b (Y b) ≠ lam-b →
      m ≤ -featureTheta lam d v+
        featureAlpha lam d v*(b-lam-v.1.1+continuationScore lam d Y b)) :
    ∀ r ∈ Ico zStart b,m*(b-r) ≤ continuationScore lam d Y b-continuationScore lam d Y r := by
  by_cases hline : continuationScore lam d Y b=lam-b
  · intro r hr
    rw [hline]
    have hc := vectorField_le_line lam d r (Y r)
    have hmul := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hr.2.le)
    change continuationScore lam d Y r ≤ lam-r at hc
    nlinarith only [hc,hmul]
  · have hess : vectorField lam d b (Y b)=essInf (controlH lam d b (Y b)) controlMeasure := by
      rcases min_choice (lam-b) (essInf (controlH lam d b (Y b)) controlMeasure) with hh | hh
      · exact False.elim (hline hh)
      · exact hh
    obtain ⟨v,hv,hval⟩ := hd.essInf_attained_in_featureSupport b (Y b)
    have hvactive : featureH hd b (Y b) v=vectorField lam d b (Y b) := hval.trans hess.symm
    exact terminal_active_control_chord hd hY hb hconcave hv hvactive (hscalar v hv hvactive hline)

 theorem completedVariationalScore_concave_of_terminal_control {lam a b m : ℝ}
    {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Ioo zStart zEnd)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hactive : ∀ r ∈ Icc zStart b,∀ v ∈ controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r) ≠ lam-r →
      1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1)
    (hm : m ≤ -1) {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hvactive : featureH hd b (Y b) v=vectorField lam d b (Y b))
    (hscalar : m ≤ -featureTheta lam d v+
      featureAlpha lam d v*(b-lam-v.1.1+continuationScore lam d Y b))
    (htwo : tailTwo b (Y b) (continuationScore lam d Y b) ≤ 0)
    (htail : tailOne b (Y b) (continuationScore lam d Y b)/(1-b) ≤ m) :
    ConcaveOn ℝ (Icc lam 1) (completedVariationalScore a lam d low Y b) := by
  have hshape := continuation_score_concave hd hY le_rfl hb.2.le hactive
  exact completedVariationalScore_high_concave hd hY ha hax ⟨hb.1.le,hb.2.le⟩ hxjoin hzjoin hactive hm
    (terminal_active_control_chord hd hY hb hshape.2 hv hvactive hscalar) htwo htail


 theorem completedVariationalScore_concave_of_active_slope_bounds {lam a b m : ℝ}
    {d : LowRankData} {low Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : 0 < a) (hax : a ≤ xHi) (hb : b ∈ Ioo zStart zEnd)
    (hxjoin : low xHi=lam-xHi) (hzjoin : continuationScore lam d Y zStart=lam-zStart)
    (hactive : ∀ r ∈ Icc zStart b,∀ v ∈ controlFeatureSupport d,
      featureH hd r (Y r) v=vectorField lam d r (Y r) →
      vectorField lam d r (Y r) ≠ lam-r →
      1 ≤ featureTheta lam d v+featureAlpha lam d v*v.1.1)
    (hm : m ≤ -1)
    (hscalar : ∀ v ∈ controlFeatureSupport d,
      featureH hd b (Y b) v=vectorField lam d b (Y b) →
      vectorField lam d b (Y b) ≠ lam-b →
      m ≤ -featureTheta lam d v+
        featureAlpha lam d v*(b-lam-v.1.1+continuationScore lam d Y b))
    (htwo : tailTwo b (Y b) (continuationScore lam d Y b) ≤ 0)
    (htail : tailOne b (Y b) (continuationScore lam d Y b)/(1-b) ≤ m) :
    ConcaveOn ℝ (Icc lam 1) (completedVariationalScore a lam d low Y b) := by
  have hshape := continuation_score_concave hd hY le_rfl hb.2.le hactive
  exact completedVariationalScore_high_concave hd hY ha hax ⟨hb.1.le,hb.2.le⟩ hxjoin hzjoin hactive hm
    (terminal_chord_of_active_slope_bound hd hY hb hshape.2 hm hscalar) htwo htail

end OptimalG.Variational
