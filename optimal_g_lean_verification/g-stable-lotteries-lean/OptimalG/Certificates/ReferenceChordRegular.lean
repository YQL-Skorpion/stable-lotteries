import OptimalG.Certificates.HessianChordBounds

/-! The accepted endpoint boxes give actual denominator regularity at every
point of the comparison chord. This also supports preservation of coefficient
signs from the reference endpoint to the matched endpoint. -/
namespace OptimalG.Certificates.Transport.HessianCell
open Set

theorem checkedClean_endpoint_chord_regular {scale : ℕ} (hs : 0<scale)
    {params : FrozenParameters} {start finish : ℤ} {slabs : List IntegerInterval}
    {c : HessianCell} (horder : start<finish)
    (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) (base : Fin 16→ℝ) (s r a : ℝ)
    (hS0 : (⟨start,finish⟩:IntegerInterval).Contains scale (base 0))
    (hS1 : (⟨start,finish⟩:IntegerInterval).Contains scale (base 0+s))
    (hbase : ∀ i,(c.fixed i).Contains scale (base i.succ))
    (hR1 : (c.fixed 0).Contains scale (base 1+r))
    (hA1 : (c.fixed 1).Contains scale (base 2+a)) :
    ∀ t∈Icc (0:ℝ) 1,∀ i∈FrozenParameters.activeTerms c.late,
      params.sourceRegular c.late i (FrozenParameters.comparisonChord base s r a t) := by
  intro t ht
  have hscalar : (⟨start,finish⟩:IntegerInterval).Contains scale
      (FrozenParameters.comparisonChord base s r a t 0) := by
    simpa only [FrozenParameters.comparisonChord,FrozenParameters.threeDirection,
      Matrix.cons_val_zero] using IntegerInterval.contains_add_segment hS0 hS1 ht
  have hfixed : ∀ i,(c.fixed i).Contains scale
      (FrozenParameters.comparisonChord base s r a t i.succ) := by
    intro i
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
  obtain ⟨box,hbox,hcheck⟩ := checkedClean_box_cover horder hslabs hc hscalar hfixed
  exact FrozenParameters.hessianCleanCheck_sourceRegular hs hbox hcheck

end OptimalG.Certificates.Transport.HessianCell
