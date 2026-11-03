import OptimalG.Certificates.TransportHessianTaylor
import OptimalG.VariationalTransportODE

/-! A nonvanishing coefficient keeps its reference sign along the genuine
comparison chord. The finite Hessian checks already certify this regularity;
no separate positive-coefficient enclosure is required. -/
namespace OptimalG.Certificates.Transport.FrozenParameters
open Set RatExpr

theorem positive_endpoint_of_continuous_nonzero {f : ℝ→ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hn : ∀ t∈Icc (0:ℝ) 1,f t≠0) (h0 : 0<f 0) : 0<f 1 := by
  by_contra hnot
  have hle : f 1≤0 := le_of_not_gt hnot
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ)≤1) hf ⟨hle,h0.le⟩
  exact hn t ht he

theorem sourceRegular_coefficient_valid {d : FrozenParameters} {late : Bool}
    {i : Fin 4} {x : Fin 16→ℝ} (h : d.sourceRegular late i x) :
    (d.coefficients late i).Valid x := by
  rcases h with ⟨hj,_,hN,_,hm,_,hD,hDn⟩
  exact ⟨⟨⟨hj,hN⟩,hm⟩,hD,hDn⟩

theorem regular_coefficient_positive_endpoint (d : FrozenParameters) (late : Bool)
    (i : Fin 4) (x : ℝ→Fin 16→ℝ) (v : Fin 16→ℝ)
    (hx : ∀ t∈Icc (0:ℝ) 1,∀ j,HasDerivAt (fun u=>x u j) (v j) t)
    (hregular : ∀ t∈Icc (0:ℝ) 1,d.sourceRegular late i (x t))
    (hzero : 0<(d.coefficients late i).eval (x 0)) :
    0<(d.coefficients late i).eval (x 1) := by
  apply positive_endpoint_of_continuous_nonzero
    (f:=fun t=>(d.coefficients late i).eval (x t)) _ _ hzero
  · intro t ht
    exact (hasDerivAt_eval_gradient (d.coefficients late i) x v t (hx t ht)
      (sourceRegular_coefficient_valid (hregular t ht))).continuousAt.continuousWithinAt
  · intro t ht
    exact sourceRegular_coefficient_ne_zero (hregular t ht)

theorem chord_coefficient_positive (d : FrozenParameters) (late : Bool)
    (base : Fin 16→ℝ) (ds eR eA : ℝ) (i : Fin 4)
    (hregular : ∀ t∈Icc (0:ℝ) 1,
      d.sourceRegular late i (comparisonChord base ds eR eA t))
    (hzero : 0<(d.coefficients late i).eval base) :
    0<(d.coefficients late i).eval (comparisonChord base ds eR eA 1) := by
  apply d.regular_coefficient_positive_endpoint late i (comparisonChord base ds eR eA)
    (threeDirection ds eR eA) (fun t _ j=>comparisonChord_hasDerivAt base ds eR eA t j)
    hregular
  simpa only [comparisonChord_zero] using hzero

theorem coefficient_positive_of_weight {rho coefficient delta w : ℝ}
    (hrho : 0<rho) (hweight : 0≤rho*Variational.referenceWeight coefficient delta w)
    (hneq : coefficient≠0) : 0<coefficient := by
  have hexp := Real.exp_pos (-delta*w)
  have hnonneg : 0≤coefficient := by
    by_contra hneg
    have hproduct := mul_neg_of_pos_of_neg (mul_pos hrho hexp) (lt_of_not_ge hneg)
    unfold Variational.referenceWeight at hweight
    nlinarith only [hproduct,hweight]
  exact lt_of_le_of_ne hnonneg (Ne.symm hneq)

end OptimalG.Certificates.Transport.FrozenParameters
