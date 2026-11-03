import OptimalG.Certificates.TransportHessianValidity
import OptimalG.VariationalTransportTaylor

/-! A finite Hessian cover implies the Taylor bound for the actual transported
coefficient logarithms. All denominator and differentiability conditions are
discharged by the accepted interval checks. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr
open scoped BigOperators
namespace FrozenParameters

noncomputable def comparisonChord (base : Fin 16→ℝ) (s r a t : ℝ) : Fin 16→ℝ :=
  fun j => base j+t*threeDirection s r a j

theorem comparisonChord_hasDerivAt (base : Fin 16→ℝ) (s r a t : ℝ) (j : Fin 16) :
    HasDerivAt (fun u => comparisonChord base s r a u j) (threeDirection s r a j) t := by
  convert! ((hasDerivAt_id t).mul_const (threeDirection s r a j)).const_add (base j) using 1 <;>
    simp [comparisonChord]

@[simp] theorem comparisonChord_zero (base : Fin 16→ℝ) (s r a : ℝ) :
    comparisonChord base s r a 0=base := by ext j; simp [comparisonChord]

theorem comparisonChord_weight (base : Fin 16→ℝ) (s r a t : ℝ) (i : Fin 4) :
    comparisonChord base s r a t ⟨12+i.val,by omega⟩=base ⟨12+i.val,by omega⟩ := by
  fin_cases i <;> simp [comparisonChord,threeDirection]

theorem checked_source_taylor {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a : ℝ)
    (hx : ∀ t∈Icc (0:ℝ) 1,∀ j,
      HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ t∈Icc (0:ℝ) 1,∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (x t i)) ∧
      d.hessianCheck scale late box rankPenalty scalarLower=true) :
    d.weightedSource late w (x 0)+d.weightedFirst late w (x 0) (threeDirection s r a)+
      ((scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))/2 ≤
        d.weightedSource late w (x 1) := by
  apply Variational.segment_second_order_lower
    (f := fun t => d.weightedSource late w (x t))
    (f' := fun t => d.weightedFirst late w (x t) (threeDirection s r a))
    (f'' := fun t => d.checkedQuadratic late (x t) s r a)
    (c := (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))
  · intro t ht
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact d.hasDerivAt_weightedSource late w x (threeDirection s r a) t (hx t ht)
      (hessianCheck_sourceRegular hs hb hc)
  · intro t ht
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact (checked_second_directional_derivative_of_check hs d late w x s r a t
      (hx t ht) (hw t ht) box hb rankPenalty scalarLower hc).1
  · intro t ht
    obtain ⟨box,hb,hc⟩ := hcover t ⟨ht.1.le,ht.2.le⟩
    exact d.hessianCheck_sound hs hb hc s r a

theorem sourceRegular_coefficient_ne_zero {d : FrozenParameters} {late : Bool}
    {i : Fin 4} {x : Fin 16→ℝ} (h : d.sourceRegular late i x) :
    (d.coefficients late i).eval x≠0 := by
  rcases h with ⟨_,hj,_,hN,_,hm,_,hD⟩
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hj hN) hm) hD

theorem weighted_log_ratio_eq (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x y : Fin 16→ℝ)
    (hx : ∀ i∈activeTerms late,d.sourceRegular late i x)
    (hy : ∀ i∈activeTerms late,d.sourceRegular late i y) :
    (∑ i∈activeTerms late,w i*Real.log
      ((d.coefficients late i).eval y/(d.coefficients late i).eval x))=
      d.weightedSource late w y-d.weightedSource late w x := by
  unfold weightedSource
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨_,hjx,_,hNx,_,hmx,_,hDx⟩ := hx i hi
  obtain ⟨_,hjy,_,hNy,_,hmy,_,hDy⟩ := hy i hi
  rw [d.logSource_eq late i x hjx hNx hmx hDx,
    d.logSource_eq late i y hjy hNy hmy hDy,
    Real.log_div (sourceRegular_coefficient_ne_zero (hy i hi))
      (sourceRegular_coefficient_ne_zero (hx i hi))]
  ring

/-- This is the second-order coefficient contribution used in B.4, directly
for the actual rational control coefficients, rather than formal symbols. -/
theorem checked_coefficient_log_ratio_lower {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a : ℝ)
    (hx : ∀ t∈Icc (0:ℝ) 1,∀ j,
      HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ t∈Icc (0:ℝ) 1,∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (x t i)) ∧
      d.hessianCheck scale late box rankPenalty scalarLower=true) :
    d.weightedFirst late w (x 0) (threeDirection s r a)+
      ((scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))/2 ≤
        ∑ i∈activeTerms late,w i*Real.log
          ((d.coefficients late i).eval (x 1)/(d.coefficients late i).eval (x 0)) := by
  have h := checked_source_taylor hs d late w x s r a hx hw rankPenalty scalarLower hcover
  have hr (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      ∀ i∈activeTerms late,d.sourceRegular late i (x t) := by
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact hessianCheck_sourceRegular hs hb hc
  rw [d.weighted_log_ratio_eq late w (x 0) (x 1)
    (hr 0 (by norm_num)) (hr 1 (by norm_num))]
  linarith only [h]

/-- Specialization to the comparison chord used by the reference argument. -/
theorem checked_chord_log_ratio_lower {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (base : Fin 16→ℝ) (s r a : ℝ)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (comparisonChord base s r a t i)) ∧
      d.hessianCheck scale late box rankPenalty scalarLower=true) :
    d.weightedFirst late (fun i => base ⟨12+i.val,by omega⟩) base (threeDirection s r a)+
      ((scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))/2 ≤
        ∑ i∈activeTerms late,base ⟨12+i.val,by omega⟩*Real.log
          ((d.coefficients late i).eval (comparisonChord base s r a 1)/
            (d.coefficients late i).eval base) := by
  simpa only [comparisonChord_zero] using checked_coefficient_log_ratio_lower hs d late
    (fun i => base ⟨12+i.val,by omega⟩) (comparisonChord base s r a) s r a
    (fun t _ j => comparisonChord_hasDerivAt base s r a t j)
    (fun t _ i => comparisonChord_weight base s r a t i) rankPenalty scalarLower hcover

end FrozenParameters
end OptimalG.Certificates.Transport
