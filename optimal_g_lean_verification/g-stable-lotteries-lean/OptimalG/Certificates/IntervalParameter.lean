import OptimalG.Certificates.IndexedBoxCover

namespace OptimalG.Certificates
open Set

/-- Closed interval parameterization includes the degenerate edge of a
triangular certificate domain, without division by zero. -/
theorem exists_unit_interval_parameter {a b x : ℝ} (hx : x∈Icc a b) :
    ∃ u∈Icc (0:ℝ) 1,x=a+u*(b-a) := by
  by_cases hzero : b-a=0
  · have hxa : x=a := by linarith only [hx.1,hx.2,hzero]
    exact ⟨0,⟨le_rfl,by norm_num⟩,by rw [hxa];ring⟩
  · have hpos : 0<b-a := lt_of_le_of_ne (by linarith only [hx.1,hx.2]) (Ne.symm hzero)
    refine ⟨(x-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hx.1) hpos.le,?_⟩,?_⟩
    · rw [div_le_iff₀ hpos]
      linarith only [hx.2]
    · field_simp [hzero]
      <;> ring

end OptimalG.Certificates
