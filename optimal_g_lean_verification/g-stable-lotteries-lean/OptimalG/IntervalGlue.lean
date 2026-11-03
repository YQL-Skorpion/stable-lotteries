import OptimalG.PolynomialCompletion
import Mathlib.Topology.Piecewise

/-! Continuous, decreasing interval gluing with exact integral additivity. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def joinAt (c : ℝ) (f g : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ c then f r else g r

theorem joinAt_left {c r : ℝ} (f g : ℝ → ℝ) (hr : r ≤ c) : joinAt c f g r=f r := by
  simp [joinAt,hr]

theorem joinAt_right {c r : ℝ} (f g : ℝ → ℝ) (hr : c ≤ r) (hc : f c=g c) : joinAt c f g r=g r := by
  by_cases he : r=c
  · subst r; simp [joinAt,hc]
  · simp [joinAt,not_le.mpr (lt_of_le_of_ne hr (Ne.symm he))]

theorem continuousOn_joinAt {a c b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a c)) (hg : ContinuousOn g (Icc c b)) (hc : f c=g c) :
    ContinuousOn (joinAt c f g) (Icc a b) := by
  apply ContinuousOn.if
  · intro r hr
    have he : r=c := by
      have hh := hr.2
      change r ∈ frontier (Iic c) at hh
      simpa only [frontier_Iic,mem_singleton_iff] using hh
    simpa only [he] using hc
  · apply hf.mono
    intro r hr
    have hh := hr.2
    change r ∈ closure (Iic c) at hh
    rw [closure_Iic] at hh
    exact ⟨hr.1.1,hh⟩
  · apply hg.mono
    intro r hr
    have hh := hr.2
    have he : {r : ℝ | ¬r ≤ c}=Ioi c := by ext r; simp
    rw [he,closure_Ioi] at hh
    exact ⟨hh,hr.1.2⟩

theorem strictAntiOn_joinAt {a c b : ℝ} {f g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : StrictAntiOn f (Icc a c)) (hg : StrictAntiOn g (Icc c b)) (hc : f c=g c) :
    StrictAntiOn (joinAt c f g) (Icc a b) := by
  intro r hr s hs hrs
  by_cases hsc : s ≤ c
  · rw [joinAt_left f g hsc,joinAt_left f g (hrs.le.trans hsc)]
    exact hf ⟨hr.1,hrs.le.trans hsc⟩ ⟨hs.1,hsc⟩ hrs
  · have hcs : c < s := lt_of_not_ge hsc
    rw [joinAt_right f g hcs.le hc]
    by_cases hrc : r ≤ c
    · rw [joinAt_left f g hrc]
      have h1 := hg ⟨le_rfl,hcb⟩ ⟨hcs.le,hs.2⟩ hcs
      have h2 := hf.antitoneOn ⟨hr.1,hrc⟩ ⟨hac,le_rfl⟩ hrc
      rw [hc] at h2
      exact h1.trans_le h2
    · rw [joinAt_right f g (le_of_not_ge hrc) hc]
      exact hg ⟨le_of_not_ge hrc,hr.2⟩ ⟨hcs.le,hs.2⟩ hrs

theorem integral_joinAt {a c b : ℝ} {f g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : ContinuousOn f (Icc a c)) (hg : ContinuousOn g (Icc c b)) (hc : f c=g c) :
    (∫ r in a..b,joinAt c f g r)=(∫ r in a..c,f r)+(∫ r in c..b,g r) := by
  have hj := continuousOn_joinAt hf hg hc
  have hi : IntervalIntegrable (joinAt c f g) volume a b :=
    hj.intervalIntegrable_of_Icc (hac.trans hcb)
  have hi1 := hi.mono_set (by rw [uIcc_of_le hac,uIcc_of_le (hac.trans hcb)]; exact Icc_subset_Icc le_rfl hcb)
  have hi2 := hi.mono_set (by rw [uIcc_of_le hcb,uIcc_of_le (hac.trans hcb)]; exact Icc_subset_Icc hac le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  congr 1
  · apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hac] at hr
    exact joinAt_left f g hr.2
  · apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hcb] at hr
    exact joinAt_right f g hr.1 hc

end OptimalG
