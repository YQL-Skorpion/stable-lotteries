import OptimalG.Certificates.TransportHessianCheck

/-! The checked Hessian is the actual second directional derivative of the
weighted logarithmic source along a chord with frozen reference coordinates. -/
namespace OptimalG.Certificates.Transport
open RatExpr
open scoped BigOperators
namespace FrozenParameters

def activeTerms (late : Bool) : Finset (Fin 4) := if late then Finset.univ else {1,3}

noncomputable def logGradient (e : E) (x v : Fin 16→ℝ) : ℝ :=
  ∑ j,(logPartial j e).eval x*v j
noncomputable def logQuadratic (e : E) (x v : Fin 16→ℝ) : ℝ :=
  ∑ j,∑ k,(logHessian j k e).eval x*v k*v j

noncomputable def sourceFirst (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x v : Fin 16→ℝ) : ℝ :=
  logGradient d.j x v+logGradient (d.numerators late i) x v+
    logGradient (d.score i) x v-logGradient (d.denominator late) x v

noncomputable def sourceEntry (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (j k : Fin 16) (x : Fin 16→ℝ) : ℝ :=
  (logHessian j k d.j).eval x+(logHessian j k (d.numerators late i)).eval x+
    (logHessian j k (d.score i)).eval x-(logHessian j k (d.denominator late)).eval x

noncomputable def sourceSecond (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x v : Fin 16→ℝ) : ℝ :=
  ∑ j,∑ k,d.sourceEntry late i j k x*v k*v j

noncomputable def sourceRegular (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x : Fin 16→ℝ) : Prop :=
  d.j.Valid x ∧ d.j.eval x≠0 ∧ (d.numerators late i).Valid x ∧
    (d.numerators late i).eval x≠0 ∧ (d.score i).Valid x ∧
    (d.score i).eval x≠0 ∧ (d.denominator late).Valid x ∧ (d.denominator late).eval x≠0

theorem hasDerivAt_logSource (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x : ℝ→Fin 16→ℝ) (v : Fin 16→ℝ) (t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (v j) t)
    (hr : d.sourceRegular late i (x t)) :
    HasDerivAt (fun u => d.logSource late i (x u)) (d.sourceFirst late i (x t) v) t := by
  rcases hr with ⟨hj,hjn,hN,hNn,hm,hmn,hD,hDn⟩
  exact (((hasDerivAt_log_gradient d.j x v t hx hj hjn).add
    (hasDerivAt_log_gradient (d.numerators late i) x v t hx hN hNn)).add
    (hasDerivAt_log_gradient (d.score i) x v t hx hm hmn)).sub
    (hasDerivAt_log_gradient (d.denominator late) x v t hx hD hDn)

theorem hasDerivAt_sourceFirst (d : FrozenParameters) (late : Bool) (i : Fin 4)
    (x : ℝ→Fin 16→ℝ) (v : Fin 16→ℝ) (t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (v j) t)
    (hr : d.sourceRegular late i (x t)) :
    HasDerivAt (fun u => d.sourceFirst late i (x u) v) (d.sourceSecond late i (x t) v) t := by
  rcases hr with ⟨hj,hjn,hN,hNn,hm,hmn,hD,hDn⟩
  have hd := (((hasDerivAt_log_hessian d.j x v t hx hj hjn).add
    (hasDerivAt_log_hessian (d.numerators late i) x v t hx hN hNn)).add
    (hasDerivAt_log_hessian (d.score i) x v t hx hm hmn)).sub
    (hasDerivAt_log_hessian (d.denominator late) x v t hx hD hDn)
  convert! hd using 1 <;> first | rfl |
    (simp only [sourceSecond,sourceEntry,add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib])

@[simp] theorem weight_eval (i : Fin 4) (x : Fin 16→ℝ) : (weight i).eval x=x ⟨12+i.val,by omega⟩ := rfl

theorem hessianEntry_eval (d : FrozenParameters) (late : Bool) (j k : Fin 16) (x : Fin 16→ℝ) :
    (d.hessianEntry late j k).eval x=
      ∑ i ∈ activeTerms late,x ⟨12+i.val,by omega⟩*d.sourceEntry late i j k x := by
  have hf : List.finRange 4=[0,1,2,3] := by decide
  have h13 : (1:Fin 4)≠3 := by decide
  have hs2 : Fin.succ (2:Fin 3)=(3:Fin 4) := by decide
  have hz : (0:E).eval x=(0:ℝ) := by change ((0:ℚ):ℝ)=0; norm_num
  cases late <;>
    simp only [hessianEntry,activeTerms,Bool.false_eq_true,if_false,if_true,hf,h13,List.foldl_cons,
      List.foldl_nil,eval_addNotation,eval_mulNotation,eval_subNotation,hz,weight_eval,
      sourceEntry,Finset.sum_insert,Finset.mem_singleton,Finset.sum_singleton,Fin.sum_univ_succ,Fin.sum_univ_zero]
  all_goals norm_num [Finset.sum_insert,Finset.sum_singleton,h13,hs2] <;> ring

noncomputable def weightedSource (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : Fin 16→ℝ) : ℝ := ∑ i ∈ activeTerms late,w i*d.logSource late i x
noncomputable def weightedFirst (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x v : Fin 16→ℝ) : ℝ := ∑ i ∈ activeTerms late,w i*d.sourceFirst late i x v

theorem hasDerivAt_weightedSource (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (v : Fin 16→ℝ) (t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (v j) t)
    (hr : ∀ i ∈ activeTerms late,d.sourceRegular late i (x t)) :
    HasDerivAt (fun u => d.weightedSource late w (x u)) (d.weightedFirst late w (x t) v) t :=
  HasDerivAt.fun_sum (fun i hi => (d.hasDerivAt_logSource late i x v t hx (hr i hi)).const_mul (w i))

private theorem weighted_quadratic_sum {n : ℕ} (A : Finset (Fin 4))
    (w : Fin 4→ℝ) (H : Fin 4→Fin n→Fin n→ℝ) (v : Fin n→ℝ) :
    (∑ i ∈ A,w i*(∑ j,∑ k,H i j k*v k*v j))=
      ∑ j,∑ k,(∑ i ∈ A,w i*H i j k)*v k*v j := by
  calc
    _=∑ i ∈ A,∑ j,∑ k,(w i*H i j k)*v k*v j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul,Finset.sum_mul]

theorem hasDerivAt_weightedFirst (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (v : Fin 16→ℝ) (t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (v j) t)
    (hr : ∀ i ∈ activeTerms late,d.sourceRegular late i (x t))
    (hw : ∀ i,(x t) ⟨12+i.val,by omega⟩=w i) :
    HasDerivAt (fun u => d.weightedFirst late w (x u) v)
      (∑ j,∑ k,(d.hessianEntry late j k).eval (x t)*v k*v j) t := by
  have hd := HasDerivAt.fun_sum (u := activeTerms late) (fun i hi =>
    (d.hasDerivAt_sourceFirst late i x v t hx (hr i hi)).const_mul (w i))
  convert! hd using 1 <;> first | rfl | skip
  simp only [hessianEntry_eval,hw,sourceSecond]
  exact (weighted_quadratic_sum (activeTerms late) w (fun i j k => d.sourceEntry late i j k (x t)) v).symm


noncomputable def threeDirection (s r a : ℝ) : Fin 16→ℝ :=
  ![s,r,a,0,0,0,0,0,0,0,0,0,0,0,0,0]

private theorem threeDirection_quadratic (H : Fin 16→Fin 16→ℝ) (s r a : ℝ) :
    (∑ j,∑ k,H j k*threeDirection s r a k*threeDirection s r a j)=
      H 0 0*s^2+2*((H 0 1+H 1 0)/2)*s*r+2*((H 0 2+H 2 0)/2)*s*a+
      H 1 1*r^2+2*((H 1 2+H 2 1)/2)*r*a+H 2 2*a^2 := by
  norm_num [threeDirection,Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

noncomputable def checkedQuadratic (d : FrozenParameters) (late : Bool)
    (x : Fin 16→ℝ) (s r a : ℝ) : ℝ :=
  (d.hessianExpressions late 0).eval x*s^2+2*(d.hessianExpressions late 1).eval x*s*r+
    2*(d.hessianExpressions late 2).eval x*s*a+(d.hessianExpressions late 3).eval x*r^2+
    2*(d.hessianExpressions late 4).eval x*r*a+(d.hessianExpressions late 5).eval x*a^2

theorem checkedQuadratic_eq (d : FrozenParameters) (late : Bool) (x : Fin 16→ℝ) (s r a : ℝ) :
    (∑ j,∑ k,(d.hessianEntry late j k).eval x*threeDirection s r a k*threeDirection s r a j)=
      d.checkedQuadratic late x s r a := by
  have hh := threeDirection_quadratic (fun j k => (d.hessianEntry late j k).eval x) s r a
  have ht : (2:E).eval x=(2:ℝ) := by change ((2:ℚ):ℝ)=2; norm_num
  simpa [checkedQuadratic,hessianExpressions,ht] using hh

/-- The finite certificate bounds the actual second derivative along the
three-dimensional comparison chord, with the reference coordinates fixed. -/
theorem checked_second_directional_derivative {scale : ℕ} (hs : 0<scale)
    (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    (x : ℝ→Fin 16→ℝ) (s r a t : ℝ)
    (hx : ∀ j,HasDerivAt (fun u => x u j) (threeDirection s r a j) t)
    (hr : ∀ i ∈ activeTerms late,d.sourceRegular late i (x t))
    (hw : ∀ i,(x t) ⟨12+i.val,by omega⟩=w i)
    (box : Fin 16→IntegerInterval) (hbox : ∀ i,(box i).Contains scale (x t i))
    (rankPenalty scalarLower : ℚ)
    (hc : d.hessianCheck scale late box rankPenalty scalarLower=true) :
    HasDerivAt (fun u => d.weightedFirst late w (x u) (threeDirection s r a))
      (d.checkedQuadratic late (x t) s r a) t ∧
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2) ≤ d.checkedQuadratic late (x t) s r a := by
  refine ⟨?_,d.hessianCheck_sound hs hbox hc s r a⟩
  have hd := d.hasDerivAt_weightedFirst late w x (threeDirection s r a) t hx hr hw
  rw [d.checkedQuadratic_eq late (x t) s r a] at hd
  exact hd

end FrozenParameters
end OptimalG.Certificates.Transport
