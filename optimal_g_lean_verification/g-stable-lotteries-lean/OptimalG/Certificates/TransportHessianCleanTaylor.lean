import OptimalG.Certificates.TransportHessianClean
import OptimalG.Certificates.TransportHessianCell

/-! Cleaned integer expressions certify the same actual coefficient Taylor
bound. Regularity comes from the separate check of original factors. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr
open scoped BigOperators
namespace FrozenParameters

theorem checkedClean_second_directional_derivative {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (box : Fin 16→IntegerInterval) (hbox : ∀ i,(box i).Contains scale (x t i))
    (rankPenalty scalarLower : ℚ)
    (hc : d.hessianCleanCheck scale late box rankPenalty scalarLower=true) :
    HasDerivAt (fun u => d.weightedFirst late w (x u) (threeDirection s r a))
      (d.checkedQuadratic late (x t) s r a) t ∧
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2)≤d.checkedQuadratic late (x t) s r a := by
  refine ⟨?_,hessianCleanCheck_sound hs hbox hc s r a⟩
  have hd := d.hasDerivAt_weightedFirst late w x (threeDirection s r a) t hx
    (hessianCleanCheck_sourceRegular hs hbox hc) hw
  rw [d.checkedQuadratic_eq late (x t) s r a] at hd
  exact hd

theorem checkedClean_source_taylor {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a : ℝ)
    (hx : ∀ t∈Icc (0:ℝ) 1,∀ j,
      HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ t∈Icc (0:ℝ) 1,∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (x t i)) ∧
      d.hessianCleanCheck scale late box rankPenalty scalarLower=true) :
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
      (hessianCleanCheck_sourceRegular hs hb hc)
  · intro t ht
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact (checkedClean_second_directional_derivative hs d late w x s r a t
      (hx t ht) (hw t ht) box hb rankPenalty scalarLower hc).1
  · intro t ht
    obtain ⟨box,hb,hc⟩ := hcover t ⟨ht.1.le,ht.2.le⟩
    exact d.hessianCleanCheck_sound hs hb hc s r a

theorem checkedClean_coefficient_log_ratio_lower {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a : ℝ)
    (hx : ∀ t∈Icc (0:ℝ) 1,∀ j,
      HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ t∈Icc (0:ℝ) 1,∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (x t i)) ∧
      d.hessianCleanCheck scale late box rankPenalty scalarLower=true) :
    d.weightedFirst late w (x 0) (threeDirection s r a)+
      ((scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))/2 ≤
        ∑ i∈activeTerms late,w i*Real.log
          ((d.coefficients late i).eval (x 1)/(d.coefficients late i).eval (x 0)) := by
  have h := checkedClean_source_taylor hs d late w x s r a hx hw rankPenalty scalarLower hcover
  have hr (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      ∀ i∈activeTerms late,d.sourceRegular late i (x t) := by
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact hessianCleanCheck_sourceRegular hs hb hc
  rw [d.weighted_log_ratio_eq late w (x 0) (x 1)
    (hr 0 (by norm_num)) (hr 1 (by norm_num))]
  linarith only [h]

/-- Specialization to the comparison chord used by the reference argument. -/
theorem checkedClean_chord_log_ratio_lower {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (base : Fin 16→ℝ) (s r a : ℝ)
    (rankPenalty scalarLower : ℚ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : Fin 16→IntegerInterval,
      (∀ i,(box i).Contains scale (comparisonChord base s r a t i)) ∧
      d.hessianCleanCheck scale late box rankPenalty scalarLower=true) :
    d.weightedFirst late (fun i => base ⟨12+i.val,by omega⟩) base (threeDirection s r a)+
      ((scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2))/2 ≤
        ∑ i∈activeTerms late,base ⟨12+i.val,by omega⟩*Real.log
          ((d.coefficients late i).eval (comparisonChord base s r a 1)/
            (d.coefficients late i).eval base) := by
  simpa only [comparisonChord_zero] using checkedClean_coefficient_log_ratio_lower hs d late
    (fun i => base ⟨12+i.val,by omega⟩) (comparisonChord base s r a) s r a
    (fun t _ j => comparisonChord_hasDerivAt base s r a t j)
    (fun t _ i => comparisonChord_weight base s r a t i) rankPenalty scalarLower hcover

end FrozenParameters
namespace HessianCell

def checkClean (scale : ℕ) (params : FrozenParameters) (slabs : List IntegerInterval)
    (c : HessianCell) : Bool :=
  slabs.all (fun slab => params.hessianCleanCheck scale c.late (c.box slab) c.rankPenalty c.scalarLower)

theorem checkedClean_box_cover {scale : ℕ} {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) {x : Fin 16→ℝ}
    (hS : (⟨start,finish⟩:IntegerInterval).Contains scale (x 0))
    (hfixed : ∀ i,(c.fixed i).Contains scale (x i.succ)) :
    ∃ b : Fin 16→IntegerInterval,(∀ i,(b i).Contains scale (x i)) ∧
      params.hessianCleanCheck scale c.late b c.rankPenalty c.scalarLower=true := by
  obtain ⟨slab,hmem,hs⟩ := integerSlabCoverCheck_sound horder hslabs hS
  refine ⟨c.box slab,?_,List.all_eq_true.mp hc slab hmem⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact hfixed j

theorem checkedClean_quadratic {scale : ℕ} (hs : 0<scale) {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) {x : Fin 16→ℝ}
    (hS : (⟨start,finish⟩:IntegerInterval).Contains scale (x 0))
    (hfixed : ∀ i,(c.fixed i).Contains scale (x i.succ)) (s r a : ℝ) :
    (c.scalarLower:ℝ)*s^2-(c.rankPenalty:ℝ)*(r^2+a^2)≤
      params.checkedQuadratic c.late x s r a := by
  obtain ⟨b,hb,hcheck⟩ := checkedClean_box_cover horder hslabs hc hS hfixed
  exact params.hessianCleanCheck_sound hs hb hcheck s r a

/-- The comparison chord may cross several scalar slabs. The finite cover
supplies the real Hessian and denominator facts at every point of the chord. -/
theorem checkedClean_chord_log_ratio {scale : ℕ} (hs : 0<scale) {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) (base : Fin 16→ℝ) (s r a : ℝ)
    (hS : ∀ t∈Icc (0:ℝ) 1,(⟨start,finish⟩:IntegerInterval).Contains scale
      (FrozenParameters.comparisonChord base s r a t 0))
    (hfixed : ∀ t∈Icc (0:ℝ) 1,∀ i,(c.fixed i).Contains scale
      (FrozenParameters.comparisonChord base s r a t i.succ)) :
    params.weightedFirst c.late (fun i => base ⟨12+i.val,by omega⟩) base
        (FrozenParameters.threeDirection s r a)+
      ((c.scalarLower:ℝ)*s^2-(c.rankPenalty:ℝ)*(r^2+a^2))/2≤
        ∑ i∈FrozenParameters.activeTerms c.late,base ⟨12+i.val,by omega⟩*Real.log
          ((params.coefficients c.late i).eval (FrozenParameters.comparisonChord base s r a 1)/
            (params.coefficients c.late i).eval base) := by
  apply params.checkedClean_chord_log_ratio_lower hs c.late base s r a c.rankPenalty c.scalarLower
  intro t ht
  exact checkedClean_box_cover horder hslabs hc (hS t ht) (hfixed t ht)

end HessianCell
end OptimalG.Certificates.Transport
