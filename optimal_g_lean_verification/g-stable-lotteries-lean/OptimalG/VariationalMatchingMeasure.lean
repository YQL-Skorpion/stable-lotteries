import OptimalG.VariationalRankMatching

/-! The derivative measure of a matched rank, with the initial displacement
retained as an atom. The extension is constant a strictly before a, not at
the possibly larger matched value gamma a. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Function
open scoped Topology

noncomputable def matchingExtension (a b : ℝ) (gamma : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r < a then a else if r ≤ b then gamma r else gamma b

 theorem matchingExtension_monotone {a b : ℝ} {gamma : ℝ → ℝ}
    (hab : a ≤ b) (hg : MonotoneOn gamma (Icc a b))
    (hmap : ∀ r ∈ Icc a b, gamma r ∈ Icc a b) : Monotone (matchingExtension a b gamma) := by
  intro r s hrs
  unfold matchingExtension
  by_cases hra : r < a
  · rw [if_pos hra]
    by_cases hsa : s < a
    · rw [if_pos hsa]
    · rw [if_neg hsa]
      split_ifs with hsb
      · exact (hmap s ⟨le_of_not_gt hsa,hsb⟩).1
      · exact (hmap b ⟨hab,le_rfl⟩).1
  · have hsa : ¬ s < a := by linarith
    rw [if_neg hra,if_neg hsa]
    by_cases hrb : r ≤ b
    · rw [if_pos hrb]
      by_cases hsb : s ≤ b
      · rw [if_pos hsb]
        exact hg ⟨le_of_not_gt hra,hrb⟩ ⟨le_of_not_gt hsa,hsb⟩ hrs
      · rw [if_neg hsb]
        exact hg ⟨le_of_not_gt hra,hrb⟩ ⟨hab,le_rfl⟩ hrb
    · have hsb : ¬ s ≤ b := by linarith
      rw [if_neg hrb,if_neg hsb]

 theorem matchingExtension_eq {a b r : ℝ} {gamma : ℝ → ℝ} (hr : r ∈ Icc a b) :
    matchingExtension a b gamma r = gamma r := by
  simp only [matchingExtension,if_neg (not_lt_of_ge hr.1),if_pos hr.2]

 theorem matching_rightLim_below {a b r : ℝ} {gamma : ℝ → ℝ} (hr : r < a) :
    rightLim (matchingExtension a b gamma) r = a := by
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT hr] with s hs
  simp only [matchingExtension,if_pos hs.2]

 theorem matching_rightLim_above {a b r : ℝ} {gamma : ℝ → ℝ} (hab : a ≤ b) (hr : b ≤ r) :
    rightLim (matchingExtension a b gamma) r = gamma b := by
  apply rightLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hrs : r < s := hs
  have hsa : ¬ s < a := by linarith
  have hsb : ¬ s ≤ b := by linarith
  simp only [matchingExtension,if_neg hsa,if_neg hsb]

 theorem matching_rightLim_left_trace {a b : ℝ} {gamma : ℝ → ℝ} :
    leftLim (rightLim (matchingExtension a b gamma)) a = a := by
  apply leftLim_eq_of_tendsto
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (matching_rightLim_below hs).symm

/-- The total derivative measure is exactly the final matched rank minus a;
this formula includes the initial atom automatically. -/
theorem matching_measure_total {a b : ℝ} {gamma : ℝ → ℝ}
    (hab : a ≤ b) (hg : MonotoneOn gamma (Icc a b))
    (hmap : ∀ r ∈ Icc a b, gamma r ∈ Icc a b) :
    (matchingExtension_monotone hab hg hmap).stieltjesFunction.measure (Icc a b) =
      ENNReal.ofReal (gamma b-a) := by
  rw [StieltjesFunction.measure_Icc]
  change ENNReal.ofReal (rightLim (matchingExtension a b gamma) b-
    leftLim (rightLim (matchingExtension a b gamma)) a) = _
  rw [matching_rightLim_above hab le_rfl,matching_rightLim_left_trace]

 theorem matching_measure_mass_bound {a b : ℝ} {gamma : ℝ → ℝ}
    (hab : a ≤ b) (hg : MonotoneOn gamma (Icc a b))
    (hmap : ∀ r ∈ Icc a b, gamma r ∈ Icc a b) :
    (matchingExtension_monotone hab hg hmap).stieltjesFunction.measure (Icc a b) ≤
      ENNReal.ofReal (b-a) := by
  rw [matching_measure_total hab hg hmap]
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_right (hmap b ⟨hab,le_rfl⟩).2 a)

 theorem matchingExtension_mem {a b : ℝ} {gamma : ℝ → ℝ}
    (hab : a ≤ b) (hmap : ∀ r ∈ Icc a b, gamma r ∈ Icc a b) (r : ℝ) :
    matchingExtension a b gamma r ∈ Icc a b := by
  unfold matchingExtension
  split_ifs with hr hbr
  · exact ⟨le_rfl,hab⟩
  · exact hmap r ⟨le_of_not_gt hr,hbr⟩
  · exact hmap b ⟨hab,le_rfl⟩

 theorem matching_rightLim_mem {a b : ℝ} {gamma : ℝ → ℝ}
    (hab : a ≤ b) (hg : MonotoneOn gamma (Icc a b))
    (hmap : ∀ r ∈ Icc a b, gamma r ∈ Icc a b) (r : ℝ) :
    rightLim (matchingExtension a b gamma) r ∈ Icc a b := by
  apply isClosed_Icc.mem_of_tendsto ((matchingExtension_monotone hab hg hmap).tendsto_rightLim r)
  exact Eventually.of_forall (matchingExtension_mem hab hmap)

/-- Taking the right-continuous representative preserves primitive matching
at every interior reference rank, even across plateaus of the competitor. -/
theorem primitive_matching_rightLim {a b : ℝ} {J Xi gamma : ℝ → ℝ}
    (hab : a ≤ b) (hJ : ContinuousOn J (Icc a b)) (hXi : ContinuousOn Xi (Icc a b))
    (hg : MonotoneOn gamma (Icc a b))
    (hmatch : ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r)
    {r : ℝ} (hr : r ∈ Ico a b) :
    J (rightLim (matchingExtension a b gamma) r) = Xi r := by
  let g := matchingExtension a b gamma
  have hmap := fun s hs => (hmatch s hs).1
  have hgmono := matchingExtension_monotone hab hg hmap
  have hG := matching_rightLim_mem hab hg hmap r
  have ht : Tendsto g (𝓝[>] r) (𝓝[Icc a b] (rightLim g r)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hgmono.tendsto_rightLim r,Eventually.of_forall (matchingExtension_mem hab hmap)⟩
  have hjlim := (hJ _ hG).tendsto.comp ht
  have htXi : Tendsto (fun s : ℝ => s) (𝓝[>] r) (𝓝[Icc a b] r) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds,?_⟩
    filter_upwards [Ioo_mem_nhdsGT hr.2] with t ht
    exact ⟨hr.1.trans ht.1.le,ht.2.le⟩
  have hXiLim : Tendsto Xi (𝓝[>] r) (𝓝 (Xi r)) :=
    (hXi _ ⟨hr.1,hr.2.le⟩).tendsto.comp htXi
  have he : (fun s => J (g s)) =ᶠ[𝓝[>] r] Xi := by
    filter_upwards [Ioo_mem_nhdsGT hr.2] with t ht
    have htab : t ∈ Icc a b := ⟨hr.1.trans ht.1.le,ht.2.le⟩
    change J (matchingExtension a b gamma t) = Xi t
    rw [matchingExtension_eq htab]
    exact (hmatch t htab).2
  exact tendsto_nhds_unique hjlim (hXiLim.congr' he.symm)

 theorem primitive_matching_rightLim_all {a b : ℝ} {J Xi gamma : ℝ → ℝ}
    (hab : a ≤ b) (hJ : ContinuousOn J (Icc a b)) (hXi : ContinuousOn Xi (Icc a b))
    (hg : MonotoneOn gamma (Icc a b))
    (hmatch : ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r)
    {r : ℝ} (hr : r ∈ Icc a b) :
    J (rightLim (matchingExtension a b gamma) r) = Xi r := by
  rcases hr.2.eq_or_lt with he | hlt
  · subst r
    rw [matching_rightLim_above hab le_rfl]
    exact (hmatch b ⟨hab,le_rfl⟩).2
  · exact primitive_matching_rightLim hab hJ hXi hg hmatch ⟨hr.1,hlt⟩

/-- Full construction of a right-continuous matching and its left trace.
The initial jump is recorded because the left trace equals a, even when
G(a)>a. No strict positivity of the competing derivative is assumed. -/
theorem exists_stieltjes_primitive_matching {a b : ℝ} {J Xi : ℝ → ℝ}
    (hab : a ≤ b) (hJ : ContinuousOn J (Icc a b)) (hJmono : MonotoneOn J (Icc a b))
    (hXi : ContinuousOn Xi (Icc a b)) (hXimono : StrictMonoOn Xi (Icc a b))
    (hleft : J a ≤ Xi a) (hright : Xi b ≤ J b) :
    ∃ G : StieltjesFunction ℝ, leftLim G a = a ∧
      ∀ r ∈ Icc a b, G r ∈ Icc a b ∧ J (G r) = Xi r := by
  obtain ⟨gamma,hmatch⟩ := exists_primitive_matching hab hJ hXimono.monotoneOn hleft hright
  have hg := (primitive_matching_strictMono hJmono hXimono hmatch).monotoneOn
  have hmap := fun r hr => (hmatch r hr).1
  let G := (matchingExtension_monotone hab hg hmap).stieltjesFunction
  refine ⟨G,matching_rightLim_left_trace,?_⟩
  intro r hr
  exact ⟨matching_rightLim_mem hab hg hmap r,primitive_matching_rightLim_all hab hJ hXi hg hmatch hr⟩

end OptimalG.Variational
