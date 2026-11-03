import OptimalG.VariationalAffinePushforward

/-! Exact pushforward identities for the full finite reference partition. -/
namespace OptimalG.Variational
open Set MeasureTheory Certificates.Transport

 theorem pushforwardDensity_test_integrable (segments : List ReferenceSegment)
    (rank : ReferenceNode → ℚ) (weight : ReferenceSegment → ℝ → ℝ) (test : ℝ → ℝ)
    (hi : ∀ seg ∈ segments, Integrable (fun r => segmentDensity seg rank (weight seg) r*test r)) :
    Integrable (fun r => pushforwardDensity segments rank weight r*test r) := by
  induction segments with
  | nil => simp [pushforwardDensity]
  | cons seg rest ih =>
      have hhead := hi seg (List.mem_cons_self)
      have htail := ih (fun t ht => hi t (List.mem_cons_of_mem seg ht))
      change Integrable (fun r => (segmentDensity seg rank (weight seg) r+
        pushforwardDensity rest rank weight r)*test r)
      simp_rw [add_mul]
      exact hhead.add htail

 theorem pushforwardDensity_integral (segments : List ReferenceSegment)
    (rank : ReferenceNode → ℚ) (weight : ReferenceSegment → ℝ → ℝ) (test : ℝ → ℝ)
    (ht : ∀ seg ∈ segments, (seg.left.z:ℝ) < seg.right.z)
    (hr : ∀ seg ∈ segments, (rank seg.left:ℝ) < rank seg.right)
    (hi : ∀ seg ∈ segments, Integrable (fun r => segmentDensity seg rank (weight seg) r*test r)) :
    (∫ r, pushforwardDensity segments rank weight r*test r) =
      (segments.map (fun seg => ∫ s in (seg.left.z:ℝ)..(seg.right.z:ℝ),
        weight seg s*test (seg.rankMap rank s))).sum := by
  induction segments with
  | nil => simp [pushforwardDensity]
  | cons seg rest ih =>
      have himem := fun t ht => hi t (List.mem_cons_of_mem seg ht)
      have htail := pushforwardDensity_test_integrable rest rank weight test himem
      change (∫ r, (segmentDensity seg rank (weight seg) r+
        pushforwardDensity rest rank weight r)*test r) = _+_
      simp_rw [add_mul]
      rw [integral_add (hi seg List.mem_cons_self) htail,
        reference_segment_density_integral seg rank (ht seg List.mem_cons_self)
          (hr seg List.mem_cons_self) (weight seg) test]
      congr 1
      exact ih (fun t ht' => ht t (List.mem_cons_of_mem seg ht'))
        (fun t ht' => hr t (List.mem_cons_of_mem seg ht')) himem

 theorem pushforwardDensity_eq_zero_outside (segments : List ReferenceSegment)
    (rank : ReferenceNode → ℚ) (weight : ReferenceSegment → ℝ → ℝ) {a b r : ℝ}
    (himage : ∀ seg ∈ segments, a ≤ (rank seg.left:ℝ) ∧ (rank seg.right:ℝ) ≤ b)
    (hr : r ∉ Icc a b) : pushforwardDensity segments rank weight r = 0 := by
  unfold pushforwardDensity
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨seg,hseg,rfl⟩ := List.mem_map.mp hv
  have hout : r ∉ Ioo (rank seg.left:ℝ) (rank seg.right:ℝ) := by
    intro h
    exact hr ⟨(himage seg hseg).1.trans h.1.le,h.2.le.trans (himage seg hseg).2⟩
  simp only [segmentDensity,if_neg hout]

 theorem pushforwardDensity_setIntegral (segments : List ReferenceSegment)
    (rank : ReferenceNode → ℚ) (weight : ReferenceSegment → ℝ → ℝ) (test : ℝ → ℝ)
    {a b : ℝ} (himage : ∀ seg ∈ segments, a ≤ (rank seg.left:ℝ) ∧ (rank seg.right:ℝ) ≤ b) :
    (∫ r, pushforwardDensity segments rank weight r*test r) =
      ∫ r in Icc a b, pushforwardDensity segments rank weight r*test r := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : r ∈ Icc a b
  · simp only [indicator_of_mem hr]
  · rw [indicator_of_notMem hr,pushforwardDensity_eq_zero_outside segments rank weight himage hr,zero_mul]

end OptimalG.Variational
