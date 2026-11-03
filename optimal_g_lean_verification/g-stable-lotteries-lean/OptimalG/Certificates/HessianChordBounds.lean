import OptimalG.Certificates.TransportHessianCleanTaylor

/-! A rectangular Hessian cover contains the whole comparison chord as
soon as it contains the two scalar/rank endpoints and all frozen inputs. -/
namespace OptimalG.Certificates
open Set
namespace IntegerInterval

theorem contains_segment {scale : ℕ} {box : IntegerInterval} {x y t : ℝ}
    (hx : box.Contains scale x) (hy : box.Contains scale y) (ht : t∈Icc (0:ℝ) 1) :
    box.Contains scale ((1-t)*x+t*y) := by
  have h0 : 0≤1-t := sub_nonneg.mpr ht.2
  have hl0 := mul_le_mul_of_nonneg_left hx.1 h0
  have hl1 := mul_le_mul_of_nonneg_left hy.1 ht.1
  have hu0 := mul_le_mul_of_nonneg_left hx.2 h0
  have hu1 := mul_le_mul_of_nonneg_left hy.2 ht.1
  constructor <;> nlinarith

theorem contains_add_segment {scale : ℕ} {box : IntegerInterval} {x d t : ℝ}
    (hx : box.Contains scale x) (hy : box.Contains scale (x+d)) (ht : t∈Icc (0:ℝ) 1) :
    box.Contains scale (x+t*d) := by
  have he : x+t*d=(1-t)*x+t*(x+d) := by ring
  rw [he]
  exact contains_segment hx hy ht

end IntegerInterval
namespace Transport.HessianCell
open scoped BigOperators

theorem checkedClean_endpoint_chord_log_ratio {scale : ℕ} (hs : 0<scale)
    {params : FrozenParameters} {start finish : ℤ} {slabs : List IntegerInterval}
    {c : HessianCell} (horder : start<finish)
    (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) (base : Fin 16→ℝ) (s r a : ℝ)
    (hS0 : (⟨start,finish⟩:IntegerInterval).Contains scale (base 0))
    (hS1 : (⟨start,finish⟩:IntegerInterval).Contains scale (base 0+s))
    (hbase : ∀ i,(c.fixed i).Contains scale (base i.succ))
    (hR1 : (c.fixed 0).Contains scale (base 1+r))
    (hA1 : (c.fixed 1).Contains scale (base 2+a)) :
    params.weightedFirst c.late (fun i=>base ⟨12+i.val,by omega⟩) base
        (FrozenParameters.threeDirection s r a)+
      ((c.scalarLower:ℝ)*s^2-(c.rankPenalty:ℝ)*(r^2+a^2))/2≤
        ∑ i∈FrozenParameters.activeTerms c.late,base ⟨12+i.val,by omega⟩*Real.log
          ((params.coefficients c.late i).eval (FrozenParameters.comparisonChord base s r a 1)/
            (params.coefficients c.late i).eval base) := by
  apply checkedClean_chord_log_ratio hs horder hslabs hc base s r a
  · intro t ht
    simpa only [FrozenParameters.comparisonChord,FrozenParameters.threeDirection,
      Matrix.cons_val_zero] using IntegerInterval.contains_add_segment hS0 hS1 ht
  · intro t ht i
    by_cases hi0 : i=0
    · subst i
      simpa [FrozenParameters.comparisonChord,FrozenParameters.threeDirection] using
        IntegerInterval.contains_add_segment (hbase 0) hR1 ht
    by_cases hi1 : i=1
    · subst i
      simpa [FrozenParameters.comparisonChord,FrozenParameters.threeDirection] using
        IntegerInterval.contains_add_segment (hbase 1) hA1 ht
    have hd : FrozenParameters.threeDirection s r a i.succ=0 := by
      fin_cases i <;> simp_all [FrozenParameters.threeDirection]
    simpa only [FrozenParameters.comparisonChord,hd,mul_zero,add_zero] using hbase i

end Transport.HessianCell
end OptimalG.Certificates
