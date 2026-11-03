import OptimalG.VariationalRepresentativeGraph

/-! Closed endpoints belong to the support of Lebesgue measure restricted
to a nonempty open interval. -/
namespace OptimalG.Variational
open Set MeasureTheory

 theorem mem_support_open_interval_of_closed {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b) :
    r ∈ (volume.restrict (Ioo a b)).support := by
  have hsub : Ioo a b ⊆ (volume.restrict (Ioo a b)).support := by
    intro t ht
    apply Measure.interior_inter_support
    refine ⟨?_,?_⟩
    · simpa only [isOpen_Ioo.interior_eq] using ht
    · simp only [Measure.support_eq_univ,mem_univ]
  have hh := closure_minimal hsub (volume.restrict (Ioo a b)).isClosed_support
  rw [closure_Ioo hab.ne] at hh
  exact hh hr

end OptimalG.Variational
