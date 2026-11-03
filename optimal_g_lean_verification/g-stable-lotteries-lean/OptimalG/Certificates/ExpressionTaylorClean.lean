import OptimalG.Certificates.ExpressionTaylorResidual
import OptimalG.Certificates.ExpressionCleanup

namespace OptimalG.Certificates.RatExpr
open Set
def midpointTaylorCleanCheck (s : ℕ) (e : RatExpr 1) (bound : ℤ) : Bool :=
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  (e.integerInterval s unit).isSome && (match e.cleanup.integerInterval s mid,(partialExpr 0 e).cleanup.integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
  | some b0,some b1,some b2 => decide (8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound)
  | _,_,_ => false)

/-- Original denominator validity is checked independently before cleaned
values and derivatives are used for the actual midpoint Taylor theorem. -/
theorem midpointTaylorCleanCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr 1) (bound : ℤ)
    (hc : e.midpointTaylorCleanCheck s bound=true) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    |e.evalOne t|≤(bound:ℝ)/(s:ℝ) := by
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  have hm : ∀ i,(mid i).Contains s (1/2:ℝ) := by
    intro i
    simpa [mid] using IntegerInterval.pointRounded_contains s (1/2)
  have hu (u : ℝ) (h : u∈Icc (0:ℝ) 1) : ∀ i,(unit i).Contains s u := by
    intro i
    apply IntegerInterval.fromRat_contains hs
    simpa [RatInterval.Contains] using h
  have hchecks : (e.integerInterval s unit).isSome=true ∧
      (match e.cleanup.integerInterval s mid,(partialExpr 0 e).cleanup.integerInterval s mid,
        (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
      | some b0,some b1,some b2 => decide (8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound)
      | _,_,_ => false)=true := Bool.and_eq_true_iff.mp hc
  obtain ⟨validBox,hv⟩ := Option.isSome_iff_exists.mp hchecks.1
  have hc := hchecks.2
  change (match e.cleanup.integerInterval s mid,(partialExpr 0 e).cleanup.integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
    | some b0,some b1,some b2 => decide (8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound)
    | _,_,_ => false)=true at hc
  cases h0 : e.cleanup.integerInterval s mid with
  | none => simp only [h0,Bool.false_eq_true] at hc
  | some b0 =>
    cases h1 : (partialExpr 0 e).cleanup.integerInterval s mid with
    | none => simp only [h0,h1,Bool.false_eq_true] at hc
    | some b1 =>
      cases h2 : (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
      | none => simp only [h0,h1,h2,Bool.false_eq_true] at hc
      | some b2 =>
        have hvalid (u : ℝ) (hu' : u∈Icc (0:ℝ) 1) :
            (partialExpr 0 e).Valid (fun _ => u) :=
          partial_valid (integerInterval_valid hs unit (fun _ => u) (hu u hu') e hv) 0
        have h := midpoint_second_order_abs_bound
          (fun u hu' => evalOne_hasDerivAt e u (partial_valid_base 0 (hvalid u hu')))
          (fun u hu' => evalOne_hasDerivAt (partialExpr 0 e) u (hvalid u hu'))
          (IntegerInterval.abs_bound hs (integerInterval_cleanup_sound hs mid (fun _ => 1/2) hm e h0))
          (IntegerInterval.abs_bound hs (integerInterval_cleanup_sound hs mid (fun _ => 1/2) hm _ h1))
          (fun u hu' => IntegerInterval.abs_bound hs
            (integerInterval_cleanup_sound hs unit (fun _ => u) (hu u hu') _ h2)) ht
        have hn : 8*b0.maxAbs+4*b1.maxAbs+b2.maxAbs≤8*bound := by
          simpa only [h0,h1,h2,decide_eq_true_eq] using hc
        have hn' : 8*(b0.maxAbs:ℝ)+4*(b1.maxAbs:ℝ)+(b2.maxAbs:ℝ)≤8*(bound:ℝ) := by
          exact_mod_cast hn
        have hs' : (0:ℝ)<s := by exact_mod_cast hs
        have hsum : (b0.maxAbs:ℝ)/s+((b1.maxAbs:ℝ)/s)/2+((b2.maxAbs:ℝ)/s)/8≤
            (bound:ℝ)/s := by
          apply (le_div_iff₀ hs').mpr
          field_simp
          linarith
        exact h.trans hsum

end OptimalG.Certificates.RatExpr
