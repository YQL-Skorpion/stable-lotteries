import OptimalG.Certificates.TransportHessianCalculus
import OptimalG.Certificates.IntegerValidity

/-! Accepted Hessian checks also validate every logarithmic factor. Thus the
calculus interpretation obtains its denominator conditions from the same
finite certificate, rather than adding regularity assumptions. -/
namespace OptimalG.Certificates.RatExpr

theorem logHessian_valid_factors {n : ℕ} {e : RatExpr n} {x : Fin n→ℝ}
    {i j : Fin n} (h : (logHessian i j e).Valid x) : e.Valid x ∧ e.eval x≠0 := by
  exact h.1.2

private theorem foldl_add_valid_terms {n : ℕ} {α : Type*} (terms : List α)
    (f : α→RatExpr n) (acc : RatExpr n) (x : Fin n→ℝ)
    (h : (terms.foldl (fun a i => a+f i) acc).Valid x) :
    acc.Valid x ∧ ∀ i∈terms,(f i).Valid x := by
  induction terms generalizing acc with
  | nil => exact ⟨h,by simp⟩
  | cons i is ih =>
    have hh := ih (acc+f i) h
    refine ⟨hh.1.1,?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hh.1.2
    · exact hh.2 j hj

end OptimalG.Certificates.RatExpr

namespace OptimalG.Certificates.Transport
open RatExpr
namespace FrozenParameters

theorem hessianEntry_valid_source {d : FrozenParameters} {late : Bool}
    {j k : Fin 16} {x : Fin 16→ℝ}
    (h : (d.hessianEntry late j k).Valid x) :
    ∀ i∈activeTerms late,d.sourceRegular late i x := by
  have hh := RatExpr.foldl_add_valid_terms
    (if late then List.finRange 4 else [1,3])
    (fun i => weight i*(logHessian j k d.j+logHessian j k (d.numerators late i)+
      logHessian j k (d.score i)-logHessian j k (d.denominator late))) 0 x h
  intro i hi
  have hmem : i∈(if late then List.finRange 4 else [1,3]) := by
    cases late <;> simp_all [activeTerms]
  have ht := (hh.2 i hmem).2
  have hj := logHessian_valid_factors ht.1.1.1
  have hN := logHessian_valid_factors ht.1.1.2
  have hm := logHessian_valid_factors ht.1.2
  have hD := logHessian_valid_factors ht.2
  exact ⟨hj.1,hj.2,hN.1,hN.2,hm.1,hm.2,hD.1,hD.2⟩

theorem hessianBounds_sourceRegular {scale : ℕ} (hs : 0<scale)
    {d : FrozenParameters} {late : Bool} {box : Fin 16→IntegerInterval}
    {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {bounds : Fin 6→IntegerInterval} (hc : d.hessianBounds scale late box=some bounds) :
    ∀ i∈activeTerms late,d.sourceRegular late i x := by
  cases h0 : (d.hessianExpressions late 0).integerInterval scale box with
  | none => simp [hessianBounds,h0] at hc
  | some b =>
    have hv := integerInterval_valid hs box x hx (d.hessianExpressions late 0) h0
    exact hessianEntry_valid_source hv

theorem hessianCheck_sourceRegular {scale : ℕ} (hs : 0<scale)
    {d : FrozenParameters} {late : Bool} {box : Fin 16→IntegerInterval}
    {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {rankPenalty scalarLower : ℚ}
    (hc : d.hessianCheck scale late box rankPenalty scalarLower=true) :
    ∀ i∈activeTerms late,d.sourceRegular late i x := by
  cases hb : d.hessianBounds scale late box with
  | none => simp [hessianCheck,hb] at hc
  | some b => exact hessianBounds_sourceRegular hs hx hb

/-- An accepted integer Hessian certificate bounds the actual second
directional derivative, with logarithmic regularity discharged internally. -/
theorem checked_second_directional_derivative_of_check {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hw : ∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (box : Fin 16→IntegerInterval) (hbox : ∀ i,(box i).Contains scale (x t i))
    (rankPenalty scalarLower : ℚ)
    (hc : d.hessianCheck scale late box rankPenalty scalarLower=true) :
    HasDerivAt (fun u => d.weightedFirst late w (x u) (threeDirection s r a))
      (d.checkedQuadratic late (x t) s r a) t ∧
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2)≤d.checkedQuadratic late (x t) s r a :=
  checked_second_directional_derivative hs d late w x s r a t hx
    (hessianCheck_sourceRegular hs hbox hc) hw box hbox rankPenalty scalarLower hc

end FrozenParameters
end OptimalG.Certificates.Transport
