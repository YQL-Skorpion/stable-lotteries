import OptimalG.IntervalGlue
import Mathlib.Analysis.Convex.Deriv

/-! Concavity survives a continuous join with a downward slope jump. -/
namespace OptimalG
open Set

theorem concaveOn_joinAt_of_cross_slopes {a b c : ℝ} {f g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ConcaveOn ℝ (Icc a c) f)
    (hg : ConcaveOn ℝ (Icc c b) g) (hjoin : f c=g c)
    (hcross : ∀ u ∈ Ico a c,∀ v ∈ Ioc c b,
      (g v-g c)/(v-c) ≤ (f c-f u)/(c-u)) :
    ConcaveOn ℝ (Icc a b) (joinAt c f g) := by
  apply concaveOn_of_slope_anti_adjacent (convex_Icc a b)
  intro x y z hx hz hxy hyz
  by_cases hzc : z ≤ c
  · have hyc := hyz.le.trans hzc
    have hxc := hxy.le.trans hyc
    rw [joinAt_left f g hxc,joinAt_left f g hyc,joinAt_left f g hzc]
    exact hf.slope_anti_adjacent ⟨hx.1,hxc⟩ ⟨(hx.1.trans hxy.le).trans hyz.le,hzc⟩ hxy hyz
  · have hcz : c < z := lt_of_not_ge hzc
    by_cases hcx : c ≤ x
    · have hcy := hcx.trans hxy.le
      rw [joinAt_right f g hcx hjoin,joinAt_right f g hcy hjoin,joinAt_right f g hcz.le hjoin]
      exact hg.slope_anti_adjacent ⟨hcx,(hxy.le.trans hyz.le).trans hz.2⟩ ⟨hcz.le,hz.2⟩ hxy hyz
    · have hxc : x < c := lt_of_not_ge hcx
      by_cases hyc : y ≤ c
      · rw [joinAt_left f g hxc.le,joinAt_left f g hyc,joinAt_right f g hcz.le hjoin]
        rcases hyc.eq_or_lt with he|hyc
        · subst y
          have hh := hcross x ⟨hx.1,hxc⟩ z ⟨hcz,hz.2⟩
          simpa only [hjoin] using hh
        · have hleft := hf.slope_anti_adjacent ⟨hx.1,hxc.le⟩ ⟨hac,le_rfl⟩ hxy hyc
          have hright := (hcross y ⟨hx.1.trans hxy.le,hyc⟩ z ⟨hcz,hz.2⟩).trans hleft
          have hl := (div_le_iff₀ (sub_pos.mpr hyc)).mp hleft
          have hr := (div_le_iff₀ (sub_pos.mpr hcz)).mp hright
          apply (div_le_iff₀ (sub_pos.mpr hyz)).mpr
          rw [hjoin] at hl
          nlinarith only [hl,hr]
      · have hcy : c < y := lt_of_not_ge hyc
        rw [joinAt_left f g hxc.le,joinAt_right f g hcy.le hjoin,joinAt_right f g hcz.le hjoin]
        have hright := hg.slope_anti_adjacent ⟨le_rfl,hcb⟩ ⟨hcz.le,hz.2⟩ hcy hyz
        have hleft := hright.trans (hcross x ⟨hx.1,hxc⟩ y ⟨hcy,hyz.le.trans hz.2⟩)
        have hl := (le_div_iff₀ (sub_pos.mpr hxc)).mp hleft
        have hr := (le_div_iff₀ (sub_pos.mpr hcy)).mp hright
        apply (le_div_iff₀ (sub_pos.mpr hxy)).mpr
        rw [hjoin] at hl
        nlinarith only [hl,hr]

theorem concaveOn_joinAt {a b c df dg : ℝ} {f g : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ConcaveOn ℝ (Icc a c) f)
    (hg : ConcaveOn ℝ (Icc c b) g) (hjoin : f c=g c)
    (hdf : HasDerivWithinAt f df (Icc a c) c)
    (hdg : HasDerivWithinAt g dg (Icc c b) c) (hjump : dg ≤ df) :
    ConcaveOn ℝ (Icc a b) (joinAt c f g) := by
  apply concaveOn_joinAt_of_cross_slopes hac hcb hf hg hjoin
  intro u hu v hv
  have hl := hf.le_slope_of_hasDerivWithinAt ⟨hu.1,hu.2.le⟩ ⟨hac,le_rfl⟩ hu.2 hdf
  have hr := hg.slope_le_of_hasDerivWithinAt ⟨le_rfl,hcb⟩ ⟨hv.1.le,hv.2⟩ hv.1 hdg
  have hh := hr.trans (hjump.trans hl)
  simpa only [slope,vsub_eq_sub,smul_eq_mul,div_eq_mul_inv,mul_comm] using hh

end OptimalG
