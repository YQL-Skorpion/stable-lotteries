import OptimalG.Certificates.ReferenceCoefficientSign

/-! The genuine coefficients occur in matched pairs: the two inactive early
terms vanish at both endpoints, and every active pair is strictly positive.
The latter follows from the nonnegative actual adjoint weight and regularity
on the entire checked comparison chord. -/
namespace OptimalG.Certificates.Transport.FrozenParameters
open Set RatExpr

theorem coefficient_zero_of_not_active (d : FrozenParameters) (late : Bool)
    (i : Fin 4) (hi : i∉activeTerms late) (x : Fin 16→ℝ) :
    (d.coefficients late i).eval x=0 := by
  cases late
  · fin_cases i <;> simp_all [activeTerms,coefficients,numerators,
      eval_mulNotation,eval_divNotation,eval]
  · simp [activeTerms] at hi

theorem chord_coefficient_pair (d : FrozenParameters) (late : Bool)
    (base : Fin 16→ℝ) (ds eR eA rho w : ℝ) (delta : Fin 4→ℝ)
    (hrho : 0<rho)
    (hweight : ∀ i,0≤rho*Variational.referenceWeight
      ((d.coefficients late i).eval base) (delta i) w)
    (hregular : ∀ t∈Icc (0:ℝ) 1,∀ i∈activeTerms late,
      d.sourceRegular late i (comparisonChord base ds eR eA t)) (i : Fin 4) :
    (((d.coefficients late i).eval (comparisonChord base ds eR eA 1)=0 ∧
      (d.coefficients late i).eval base=0) ∨
      (0<(d.coefficients late i).eval (comparisonChord base ds eR eA 1) ∧
        0<(d.coefficients late i).eval base)) := by
  by_cases hi : i∈activeTerms late
  · have hbase : d.sourceRegular late i base := by
      simpa only [comparisonChord_zero] using hregular 0 (by norm_num) i hi
    have h0 := coefficient_positive_of_weight hrho (hweight i)
      (sourceRegular_coefficient_ne_zero hbase)
    exact Or.inr ⟨d.chord_coefficient_positive late base ds eR eA i
      (fun t ht=>hregular t ht i hi) h0,h0⟩
  · exact Or.inl ⟨d.coefficient_zero_of_not_active late i hi _,
      d.coefficient_zero_of_not_active late i hi _⟩

end OptimalG.Certificates.Transport.FrozenParameters
