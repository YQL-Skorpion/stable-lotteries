import OptimalG.VariationalIntegratingFactor
import OptimalG.VariationalLogDeficit

/-! Absolute continuity of the actual logarithmic deficit follows from the
continuation's Lipschitz regularity and strict positivity on a compact interval. -/
namespace OptimalG.Variational
open Set Real MeasureTheory
open scoped NNReal

 theorem absolutelyContinuous_log {a b : ℝ} {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpositive : ∀ r ∈ uIcc a b, 0 < f r) :
    AbsolutelyContinuousOnInterval (fun r => log (f r)) a b := by
  obtain ⟨r0,hr0,hmin⟩ := isCompact_uIcc.exists_isMinOn
    (show (uIcc a b).Nonempty from ⟨a,by simp⟩) hf.continuousOn
  obtain ⟨M,hM⟩ := hf.exists_bound
  have hlog : ContDiffOn ℝ 1 log (Icc (f r0) M) := by
    apply Real.contDiffOn_log.mono
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff]
    exact ne_of_gt ((hpositive r0 hr0).trans_le hx.1)
  obtain ⟨K,hK⟩ := hlog.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply absolutelyContinuous_comp_lipschitz hf hK
  intro r hr
  refine ⟨hmin hr,?_⟩
  have hm : |f r| ≤ M := by simpa only [Real.norm_eq_abs] using hM r hr
  exact (le_abs_self _).trans hm

 theorem logDeficit_AC {M S a b : ℝ} {Y z : ℝ → ℝ}
    (hYz : AbsolutelyContinuousOnInterval (fun r => Y (z r)) a b)
    (hpositive : ∀ r ∈ uIcc a b, 0 < M-S-Y (z r)) :
    AbsolutelyContinuousOnInterval (logDeficit M S Y z) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => M-S) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  exact absolutelyContinuous_log (hc.sub hYz) hpositive

 theorem logDeficit_AC_of_lipschitz {M S a b : ℝ} {Y z : ℝ → ℝ}
    {KY Kz : ℝ≥0} {domain : Set ℝ}
    (hY : LipschitzOnWith KY Y domain) (hz : LipschitzOnWith Kz z (uIcc a b))
    (hmap : MapsTo z (uIcc a b) domain)
    (hpositive : ∀ r ∈ uIcc a b, 0 < M-S-Y (z r)) :
    AbsolutelyContinuousOnInterval (logDeficit M S Y z) a b := by
  exact logDeficit_AC ((hY.comp hz hmap).absolutelyContinuousOnInterval) hpositive

end OptimalG.Variational
