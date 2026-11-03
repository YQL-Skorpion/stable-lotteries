import OptimalG.Certificates.TransportHessianCleanTaylor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-! Accepted denominator regularity gives genuine bounded logarithmic
sources on every covered Hessian cell. The weights are coordinates of the
same compact box, so no additional numerical weight bounds are required. -/
namespace OptimalG.Certificates
open Set
open scoped BigOperators

namespace RatExpr

theorem continuousAt_eval_of_valid {n : ℕ} {e : RatExpr n} {x : Fin n→ℝ}
    (hv : e.Valid x) : ContinuousAt (fun y=>e.eval y) x := by
  induction e with
  | const q => exact continuousAt_const
  | var i => exact (continuous_apply i).continuousAt
  | neg e ih => exact (ih hv).neg
  | add e f ihe ihf => exact (ihe hv.1).add (ihf hv.2)
  | mul e f ihe ihf => exact (ihe hv.1).mul (ihf hv.2)
  | inv e ih => exact (ih hv.1).inv₀ hv.2

end RatExpr
namespace IntegerInterval

theorem box_isCompact {n scale : ℕ} (hs : 0<scale) (box : Fin n→IntegerInterval) :
    IsCompact {x : Fin n→ℝ | ∀ i,(box i).Contains scale (x i)} := by
  have hs' : (0:ℝ)<scale := by exact_mod_cast hs
  have he : {x : Fin n→ℝ | ∀ i,(box i).Contains scale (x i)}=
      Icc (fun i=>(box i).lo/(scale:ℝ)) (fun i=>(box i).hi/(scale:ℝ)) := by
    ext x
    constructor
    · intro hx
      exact ⟨fun i=>lower_bound hs (hx i),fun i=>upper_bound hs (hx i)⟩
    · rintro ⟨hl,hu⟩ i
      exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hs').mp (hl i),
        by simpa only [mul_comm] using (le_div_iff₀ hs').mp (hu i)⟩
  rw [he]
  exact isCompact_Icc

end IntegerInterval
namespace Transport
namespace FrozenParameters

theorem continuousAt_logSource {d : FrozenParameters} {late : Bool} {i : Fin 4}
    {x : Fin 16→ℝ} (hr : d.sourceRegular late i x) :
    ContinuousAt (fun y=>d.logSource late i y) x := by
  rcases hr with ⟨hj,hjn,hN,hNn,hm,hmn,hD,hDn⟩
  exact (((RatExpr.continuousAt_eval_of_valid hj).log hjn).add
    ((RatExpr.continuousAt_eval_of_valid hN).log hNn) |>.add
    ((RatExpr.continuousAt_eval_of_valid hm).log hmn)).sub
    ((RatExpr.continuousAt_eval_of_valid hD).log hDn)

end FrozenParameters
namespace HessianCell

theorem checkedClean_weightedSource_bounded {scale : ℕ} (hs : 0<scale)
    {params : FrozenParameters} {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) :
    ∃ B : ℝ,0≤B ∧ ∀ x : Fin 16→ℝ,
      (⟨start,finish⟩:IntegerInterval).Contains scale (x 0) →
      (∀ j,(c.fixed j).Contains scale (x j.succ)) →
      |params.weightedSource c.late (fun i=>x ⟨12+i.val,by omega⟩) x|≤B := by
  let box := c.box ⟨start,finish⟩
  let K : Set (Fin 16→ℝ) := {x | ∀ i,(box i).Contains scale (x i)}
  have hcompact : IsCompact K := IntegerInterval.box_isCompact hs box
  have hregular (x : Fin 16→ℝ) (hx : x∈K) :
      ∀ i∈FrozenParameters.activeTerms c.late,params.sourceRegular c.late i x := by
    obtain ⟨b,hb,hcheck⟩ := checkedClean_box_cover horder hslabs hc (hx 0) (fun j=>hx j.succ)
    exact FrozenParameters.hessianCleanCheck_sourceRegular hs hb hcheck
  have hcont : ContinuousOn
      (fun x : Fin 16→ℝ=>params.weightedSource c.late (fun i=>x ⟨12+i.val,by omega⟩) x) K := by
    change ContinuousOn (fun x : Fin 16→ℝ=>∑ i∈FrozenParameters.activeTerms c.late,
      x ⟨12+i.val,by omega⟩*params.logSource c.late i x) K
    apply continuousOn_finsetSum
    intro i hi
    apply (continuous_apply (⟨12+i.val,by omega⟩:Fin 16)).continuousOn.mul
    intro x hx
    exact (FrozenParameters.continuousAt_logSource (hregular x hx i hi)).continuousWithinAt
  obtain ⟨B,hB⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x hS hfixed
  have hx : x∈K := by
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hS
    · exact hfixed j
  simpa only [Real.norm_eq_abs] using (hB x hx).trans (le_max_left B 0)


/-- With the same frozen weights, the actual coefficient log-ratio sum is
bounded by twice the bound for a single weighted source. -/
theorem checkedClean_weighted_log_ratio_bounded {scale : ℕ} (hs : 0<scale)
    {params : FrozenParameters} {start finish : ℤ} {slabs : List IntegerInterval} {c : HessianCell}
    (horder : start<finish) (hslabs : integerSlabCoverCheck start finish slabs=true)
    (hc : c.checkClean scale params slabs=true) :
    ∃ B : ℝ,0≤B ∧ ∀ x y : Fin 16→ℝ,
      (⟨start,finish⟩:IntegerInterval).Contains scale (x 0) →
      (∀ j,(c.fixed j).Contains scale (x j.succ)) →
      (⟨start,finish⟩:IntegerInterval).Contains scale (y 0) →
      (∀ j,(c.fixed j).Contains scale (y j.succ)) →
      (∀ i : Fin 4,y ⟨12+i.val,by omega⟩=x ⟨12+i.val,by omega⟩) →
      |∑ i∈FrozenParameters.activeTerms c.late,x ⟨12+i.val,by omega⟩*Real.log
        ((params.coefficients c.late i).eval y/(params.coefficients c.late i).eval x)|≤2*B := by
  obtain ⟨B,hB0,hB⟩ := checkedClean_weightedSource_bounded hs horder hslabs hc
  refine ⟨B,hB0,?_⟩
  intro x y hxS hxf hyS hyf hw
  obtain ⟨bx,hbx,hcx⟩ := checkedClean_box_cover horder hslabs hc hxS hxf
  obtain ⟨byy,hby,hcy⟩ := checkedClean_box_cover horder hslabs hc hyS hyf
  have hrx := FrozenParameters.hessianCleanCheck_sourceRegular hs hbx hcx
  have hry := FrozenParameters.hessianCleanCheck_sourceRegular hs hby hcy
  rw [params.weighted_log_ratio_eq c.late (fun i=>x ⟨12+i.val,by omega⟩) x y hrx hry]
  have he : (fun i : Fin 4=>x ⟨12+i.val,by omega⟩)=(fun i : Fin 4=>y ⟨12+i.val,by omega⟩) :=
    funext (fun i=>(hw i).symm)
  have hby' : |params.weightedSource c.late (fun i=>x ⟨12+i.val,by omega⟩) y|≤B := by
    rw [he]
    exact hB y hyS hyf
  exact (abs_sub _ _).trans (by linarith only [hby',hB x hxS hxf])

end HessianCell
end Transport
end OptimalG.Certificates
