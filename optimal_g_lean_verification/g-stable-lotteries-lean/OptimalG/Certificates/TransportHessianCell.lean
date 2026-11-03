import OptimalG.Certificates.TransportHessianTaylor
import OptimalG.Certificates.IntegerSlabCover

/-! A shared finite scalar partition combines the checked sixteen-input
Hessians into an actual coefficient Taylor bound on a whole reference cell. -/
namespace OptimalG.Certificates.Transport
open Set RatExpr
open scoped BigOperators

structure HessianCell where
  zLo : ℚ
  zHi : ℚ
  late : Bool
  fixed : Fin 15→IntegerInterval
  rankPenalty : ℚ
  scalarLower : ℚ

namespace HessianCell

def box (c : HessianCell) (slab : IntegerInterval) : Fin 16→IntegerInterval :=
  Fin.cases slab c.fixed

def check (scale : ℕ) (params : FrozenParameters) (slabs : List IntegerInterval)
    (c : HessianCell) : Bool :=
  slabs.all (fun slab => params.hessianCheck scale c.late (c.box slab) c.rankPenalty c.scalarLower)

theorem checked_box_cover {scale : ℕ} {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.check scale params slabs=true) {x : Fin 16→ℝ}
    (hS : (⟨start,finish⟩:IntegerInterval).Contains scale (x 0))
    (hfixed : ∀ i,(c.fixed i).Contains scale (x i.succ)) :
    ∃ b : Fin 16→IntegerInterval,(∀ i,(b i).Contains scale (x i)) ∧
      params.hessianCheck scale c.late b c.rankPenalty c.scalarLower=true := by
  obtain ⟨slab,hmem,hs⟩ := integerSlabCoverCheck_sound horder hslabs hS
  refine ⟨c.box slab,?_,List.all_eq_true.mp hc slab hmem⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact hfixed j

theorem checked_quadratic {scale : ℕ} (hs : 0<scale) {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.check scale params slabs=true) {x : Fin 16→ℝ}
    (hS : (⟨start,finish⟩:IntegerInterval).Contains scale (x 0))
    (hfixed : ∀ i,(c.fixed i).Contains scale (x i.succ)) (s r a : ℝ) :
    (c.scalarLower:ℝ)*s^2-(c.rankPenalty:ℝ)*(r^2+a^2)≤
      params.checkedQuadratic c.late x s r a := by
  obtain ⟨b,hb,hcheck⟩ := checked_box_cover horder hslabs hc hS hfixed
  exact params.hessianCheck_sound hs hb hcheck s r a

/-- The comparison chord may cross several scalar slabs. The finite cover
supplies the real Hessian and denominator facts at every point of the chord. -/
theorem checked_chord_log_ratio {scale : ℕ} (hs : 0<scale) {params : FrozenParameters}
    {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.check scale params slabs=true) (base : Fin 16→ℝ) (s r a : ℝ)
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
  apply params.checked_chord_log_ratio_lower hs c.late base s r a c.rankPenalty c.scalarLower
  intro t ht
  exact checked_box_cover horder hslabs hc (hS t ht) (hfixed t ht)

end HessianCell
end OptimalG.Certificates.Transport
