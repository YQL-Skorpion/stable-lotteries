import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.Monotone

/-! Equal-primitive matching for arbitrary monotone Lipschitz primitives.
No differentiability or strict positivity of the competing score is assumed.
The chosen matching is strictly increasing; plateaus of the primitive become
jumps of the matching, which are retained later as a Stieltjes measure. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal Topology

/-- A continuous primitive attains every level of the reference primitive
between the two endpoint barriers. -/
theorem exists_primitive_matching {a b : ℝ} {J Xi : ℝ → ℝ}
    (hab : a ≤ b) (hJ : ContinuousOn J (Icc a b))
    (hXi : MonotoneOn Xi (Icc a b)) (hleft : J a ≤ Xi a) (hright : Xi b ≤ J b) :
    ∃ gamma : ℝ → ℝ, ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r := by
  have hex : ∀ r ∈ Icc a b, ∃ s ∈ Icc a b, J s = Xi r := by
    intro r hr
    apply intermediate_value_Icc hab hJ
    exact ⟨hleft.trans (hXi ⟨le_rfl,hab⟩ hr hr.1),
      (hXi hr ⟨hab,le_rfl⟩ hr.2).trans hright⟩
  classical
  let gamma : ℝ → ℝ := fun r => if hr : r ∈ Icc a b then (hex r hr).choose else a
  refine ⟨gamma,?_⟩
  intro r hr
  simpa only [gamma,dif_pos hr] using (hex r hr).choose_spec

/-- Any matching of a strictly increasing reference is strictly increasing,
even when the competing primitive has intervals on which it is constant. -/
theorem primitive_matching_strictMono {a b : ℝ} {J Xi gamma : ℝ → ℝ}
    (hJ : MonotoneOn J (Icc a b)) (hXi : StrictMonoOn Xi (Icc a b))
    (hmatch : ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r) :
    StrictMonoOn gamma (Icc a b) := by
  intro r hr s hs hrs
  by_contra hn
  have hh := hJ (hmatch s hs).1 (hmatch r hr).1 (le_of_not_gt hn)
  rw [(hmatch s hs).2,(hmatch r hr).2] at hh
  exact (not_le_of_gt (hXi hr hs hrs)) hh

/-- A lower increment bound on the reference and a Lipschitz bound on the
competitor give the quantitative lower increment bound for the inverse map. -/
theorem primitive_matching_growth {a b m : ℝ} {M : ℝ≥0} {J Xi gamma : ℝ → ℝ}
    (hJmono : MonotoneOn J (Icc a b)) (hJlip : LipschitzOnWith M J (Icc a b))
    (hXi : StrictMonoOn Xi (Icc a b))
    (hgrowth : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → m*(s-r) ≤ Xi s-Xi r)
    (hmatch : ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r) :
    ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → m*(s-r) ≤ (M:ℝ)*(gamma s-gamma r) := by
  have hg := (primitive_matching_strictMono hJmono hXi hmatch).monotoneOn
  intro r hr s hs hrs
  have hlip := hJlip.dist_le_mul (gamma s) (hmatch s hs).1 (gamma r) (hmatch r hr).1
  have hgm := hg hr hs hrs
  have hJm := hJmono (hmatch r hr).1 (hmatch s hs).1 hgm
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hJm),
    abs_of_nonneg (sub_nonneg.mpr hgm),(hmatch s hs).2,(hmatch r hr).2] at hlip
  exact (hgrowth r hr s hs hrs).trans hlip

/-- An injective map with a Lipschitz inverse on its image pulls back every
Lebesgue null set to a null set. This includes discontinuous monotone maps. -/
theorem null_preimage_of_inverse_lipschitz {s N : Set ℝ} {gamma : ℝ → ℝ} {K : ℝ≥0}
    (hinj : InjOn gamma s)
    (hbound : ∀ r ∈ s, ∀ t ∈ s, dist r t ≤ K*dist (gamma r) (gamma t))
    (hN : volume N = 0) : volume (gamma ⁻¹' N ∩ s) = 0 := by
  let eta := Function.invFunOn gamma s
  have he : ∀ r ∈ s, eta (gamma r) = r := hinj.leftInvOn_invFunOn
  have hLip : LipschitzOnWith K eta (gamma '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨r,hr,rfl⟩ _ ⟨t,ht,rfl⟩
    rw [he r hr,he t ht]
    exact hbound r hr t ht
  have hsub : gamma ⁻¹' N ∩ s ⊆ eta '' (N ∩ gamma '' s) := by
    intro r hr
    exact ⟨gamma r,⟨hr.1,mem_image_of_mem gamma hr.2⟩,he r hr.2⟩
  have hzero : volume (N ∩ gamma '' s) = 0 := measure_mono_null inter_subset_left hN
  have himg := (hLip.mono (show N ∩ gamma '' s ⊆ gamma '' s from inter_subset_right)).hausdorffMeasure_image_le (d:=1) (by norm_num)
  rw [hausdorffMeasure_real,hzero,mul_zero] at himg
  exact measure_mono_null hsub (le_antisymm himg bot_le)

 theorem ae_pullback_of_inverse_lipschitz {s : Set ℝ} {gamma : ℝ → ℝ} {K : ℝ≥0}
    (hs : MeasurableSet s) (hinj : InjOn gamma s)
    (hbound : ∀ r ∈ s, ∀ t ∈ s, dist r t ≤ K*dist (gamma r) (gamma t))
    {P : ℝ → Prop} (hP : ∀ᵐ r ∂volume, P r) : ∀ᵐ r ∂volume.restrict s, P (gamma r) := by
  apply ae_iff.mpr
  rw [Measure.restrict_apply' hs]
  exact null_preimage_of_inverse_lipschitz hinj hbound (ae_iff.mp hP)

/-- Quantitative matching makes the pullback statement applicable directly
with inverse Lipschitz constant M/m. -/
theorem primitive_matching_inverse_bound {a b m : ℝ} {M : ℝ≥0} {gamma : ℝ → ℝ}
    (hm : 0 < m) (hmono : MonotoneOn gamma (Icc a b))
    (hgrowth : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s →
      m*(s-r) ≤ (M:ℝ)*(gamma s-gamma r)) :
    ∀ r ∈ Icc a b, ∀ s ∈ Icc a b,
      dist r s ≤ ((M:ℝ)/m)*dist (gamma r) (gamma s) := by
  intro r hr s hs
  wlog hrs : r ≤ s generalizing r s
  · simpa only [dist_comm] using this s hs r hr (le_of_not_ge hrs)
  have hg := hmono hr hs hrs
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hrs),
    abs_of_nonpos (sub_nonpos.mpr hg)]
  have h := hgrowth r hr s hs hrs
  have hh : (s-r)*m ≤ (M:ℝ)*(gamma s-gamma r) := by nlinarith only [h]
  have hdiv := (le_div_iff₀ hm).2 hh
  convert! hdiv using 1 <;> ring

end OptimalG.Variational
