import OptimalG.Certificates.ExpressionTaylorResidual
import OptimalG.Certificates.ExpressionCleanup
import OptimalG.VariationalTransportRemainder

/-! Positive rational functions with a kernel-checked lower bound on the
curvature of their negative logarithm. Original denominators are checked
before simplified derivative expressions are used. -/
namespace OptimalG.Certificates.RatExpr
open Set

def negativeLogCurvatureCheck (scale : ℕ) (e : RatExpr 1)
    (box : IntegerInterval) (curvature : ℚ) : Bool :=
  match e.integerInterval scale (fun _ => box) with
  | none => false
  | some out => decide (0<out.lo) &&
      (-logHessian 0 0 e-.const curvature).cleanup.integerLowerCheck scale (fun _ => box) 0

theorem negativeLogCurvatureCheck_sound {scale : ℕ} (hs : 0<scale)
    (e : RatExpr 1) (box : IntegerInterval) (curvature : ℚ)
    (hc : e.negativeLogCurvatureCheck scale box curvature=true) {s : ℝ}
    (hx : box.Contains scale s) :
    e.Valid (fun _ => s) ∧ 0<e.evalOne s ∧
      (curvature:ℝ)< -(logHessian 0 0 e).evalOne s := by
  cases he : e.integerInterval scale (fun _ => box) with
  | none => simp [negativeLogCurvatureCheck,he] at hc
  | some out =>
    have hh : (0<out.lo) ∧
        (-logHessian 0 0 e-.const curvature).cleanup.integerLowerCheck scale (fun _ => box) 0=true := by
      simpa only [negativeLogCurvatureCheck,he,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    have hval := integerInterval_sound hs (fun _ => box) (fun _ => s) (fun _ => hx) e he
    have hl := integerLowerCheck_sound hs (-logHessian 0 0 e-.const curvature).cleanup
      (fun _ => box) 0 hh.2 (fun _ => s) (fun _ => hx)
    simp only [Int.cast_zero,zero_div,cleanup_eval,eval_subNotation,eval] at hl
    exact ⟨integerInterval_valid hs _ _ (fun _ => hx) e he,
      IntegerInterval.positive hs hval hh.1,by exact sub_pos.mp hl⟩

/-- A finite cover can change cells along the chord; every accepted cell
certifies the actual logarithmic second derivative at its real points. -/
theorem negativeLogCurvature_taylor {scale : ℕ} (hs : 0<scale)
    (e : RatExpr 1) (curvature : ℚ) (base ds : ℝ)
    (hcover : ∀ t∈Icc (0:ℝ) 1,∃ box : IntegerInterval,
      box.Contains scale (base+t*ds) ∧
        e.negativeLogCurvatureCheck scale box curvature=true) :
    -Real.log (e.evalOne base)-(logPartial 0 e).evalOne base*ds+
      (curvature:ℝ)*ds^2/2≤ -Real.log (e.evalOne (base+ds)) := by
  have facts (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      e.Valid (fun _ => base+t*ds) ∧ 0<e.evalOne (base+t*ds) ∧
        (curvature:ℝ)< -(logHessian 0 0 e).evalOne (base+t*ds) := by
    obtain ⟨box,hb,hc⟩ := hcover t ht
    exact negativeLogCurvatureCheck_sound hs e box curvature hc hb
  have hx (t : ℝ) (i : Fin 1) :
      HasDerivAt (fun u : ℝ => base+u*ds) ds t := by
    convert! ((hasDerivAt_id t).mul_const ds).const_add base using 1 <;> simp only [one_mul]
  have h := Variational.segment_second_order_lower
    (f := fun t => -Real.log (e.evalOne (base+t*ds)))
    (f' := fun t => -(logPartial 0 e).evalOne (base+t*ds)*ds)
    (f'' := fun t => -(logHessian 0 0 e).evalOne (base+t*ds)*ds^2)
    (c := (curvature:ℝ)*ds^2)
    (by
      intro t ht
      have hd := (hasDerivAt_log_gradient e (fun u _ => base+u*ds) (fun _ => ds) t
        (hx t) (facts t ht).1 (ne_of_gt (facts t ht).2.1)).neg
      convert! hd using 1 <;>
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,mul_zero,add_zero,neg_mul,evalOne])
    (by
      intro t ht
      have hd := (hasDerivAt_log_hessian e (fun u _ => base+u*ds) (fun _ => ds) t
        (hx t) (facts t ht).1 (ne_of_gt (facts t ht).2.1)).neg
      convert! hd using 1 <;>
        simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,mul_zero,add_zero,neg_mul,
          evalOne,pow_two,mul_assoc] <;> rfl)
    (by
      intro t ht
      exact mul_le_mul_of_nonneg_right (facts t ⟨ht.1.le,ht.2.le⟩).2.2.le (sq_nonneg ds))
  simpa only [zero_mul,add_zero,one_mul,sub_eq_add_neg,neg_mul] using h

end OptimalG.Certificates.RatExpr
