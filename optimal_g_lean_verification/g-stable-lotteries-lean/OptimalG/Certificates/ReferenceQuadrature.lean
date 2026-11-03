import OptimalG.Certificates.MidpointQuadrature
import OptimalG.Certificates.ExpressionTaylorClean
import OptimalG.Certificates.IntegerTranscendental

/-! Exact midpoint quadrature certificates for the actual rational reference
field. Accepted bounds enclose a Lebesgue interval integral, not a sampled sum. -/
namespace OptimalG.Certificates.RatExpr
open Set MeasureTheory

def midpointIntegralCheck (s : ℕ) (e : RatExpr 1) (out : IntegerInterval) : Bool :=
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  (e.integerInterval s unit).isSome &&
    (match e.cleanup.integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
    | some b0,some b2 => decide
        (24*out.lo≤24*b0.lo-b2.maxAbs ∧ 24*b0.hi+b2.maxAbs≤24*out.hi)
    | _,_ => false)

theorem midpointIntegralCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr 1)
    (out : IntegerInterval) (hc : e.midpointIntegralCheck s out=true) :
    out.Contains s (∫ t in (0:ℝ)..1,e.evalOne t) := by
  let mid : Fin 1→IntegerInterval := fun _ => IntegerInterval.pointRounded s (1/2)
  let unit : Fin 1→IntegerInterval := fun _ => IntegerInterval.fromRat s ⟨0,1⟩
  have hm : ∀ i,(mid i).Contains s (1/2:ℝ) := by
    intro i
    simpa [mid] using IntegerInterval.pointRounded_contains s (1/2)
  have hu (u : ℝ) (h : u∈Icc (0:ℝ) 1) : ∀ i,(unit i).Contains s u := by
    intro i
    exact IntegerInterval.fromRat_contains hs (by simpa [RatInterval.Contains] using h)
  have hh := Bool.and_eq_true_iff.mp hc
  obtain ⟨validBox,hv⟩ := Option.isSome_iff_exists.mp hh.1
  have hvalid (u : ℝ) (h : u∈Icc (0:ℝ) 1) : e.Valid (fun _ => u) :=
    integerInterval_valid hs unit (fun _ => u) (hu u h) e hv
  have hh := hh.2
  change (match e.cleanup.integerInterval s mid,
      (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
    | some b0,some b2 => decide
        (24*out.lo≤24*b0.lo-b2.maxAbs ∧ 24*b0.hi+b2.maxAbs≤24*out.hi)
    | _,_ => false)=true at hh
  cases h0 : e.cleanup.integerInterval s mid with
  | none => simp only [h0,Bool.false_eq_true] at hh
  | some b0 =>
    cases h2 : (partialExpr 0 (partialExpr 0 e)).cleanup.integerInterval s unit with
    | none => simp only [h0,h2,Bool.false_eq_true] at hh
    | some b2 =>
      have hn : 24*out.lo≤24*b0.lo-b2.maxAbs ∧ 24*b0.hi+b2.maxAbs≤24*out.hi := by
        simpa only [h0,h2,decide_eq_true_eq] using hh
      have hmid := integerInterval_cleanup_sound hs mid (fun _ => 1/2) hm e h0
      change b0.Contains s (e.evalOne (1/2)) at hmid
      have herr := midpoint_integral_abs_error
        (fun t ht => evalOne_hasDerivAt e t (hvalid t ht))
        (fun t ht => evalOne_hasDerivAt (partialExpr 0 e) t (partial_valid (hvalid t ht) 0))
        (fun t ht => IntegerInterval.abs_bound hs
          (integerInterval_cleanup_sound hs unit (fun _ => t) (hu t ht) _ h2))
      have hs' : (0:ℝ)<s := by exact_mod_cast hs
      have he : |(s:ℝ)*((∫ t in (0:ℝ)..1,e.evalOne t)-e.evalOne (1/2))|≤
          (b2.maxAbs:ℝ)/24 := by
        rw [abs_mul,abs_of_pos hs']
        calc
          _≤(s:ℝ)*(((b2.maxAbs:ℝ)/s)/24) := mul_le_mul_of_nonneg_left herr hs'.le
          _=(b2.maxAbs:ℝ)/24 := by field_simp
      have hnlo : 24*(out.lo:ℝ)≤24*(b0.lo:ℝ)-(b2.maxAbs:ℝ) := by exact_mod_cast hn.1
      have hnhi : 24*(b0.hi:ℝ)+(b2.maxAbs:ℝ)≤24*(out.hi:ℝ) := by exact_mod_cast hn.2
      have he' := abs_le.mp he
      constructor <;> dsimp [IntegerInterval.Contains] at hmid ⊢ <;>
        nlinarith [hmid.1,hmid.2,he'.1,he'.2]

def midpointScaledIntegralCheck (s k : ℕ) (e : RatExpr 1) (width : ℚ)
    (mean out : IntegerInterval) : Bool :=
  e.midpointIntegralCheck (k*s) mean &&
    (IntegerInterval.mulRounded (k*s) (IntegerInterval.pointRounded (k*s) width) mean).subsetCheck (out.rescale k)

theorem midpointScaledIntegralCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (e : RatExpr 1) (width : ℚ) (mean out : IntegerInterval)
    (hc : e.midpointScaledIntegralCheck s k width mean out=true) :
    out.Contains s ((width:ℝ)*(∫ t in (0:ℝ)..1,e.evalOne t)) := by
  have hh := Bool.and_eq_true_iff.mp hc
  apply (IntegerInterval.rescale_contains_iff hk s out _).mp
  exact IntegerInterval.subsetCheck_sound
    (IntegerInterval.mulRounded_contains (Nat.mul_pos hk hs)
      (IntegerInterval.pointRounded_contains (k*s) width)
      (midpointIntegralCheck_sound (Nat.mul_pos hk hs) e mean hh.1)) hh.2

end OptimalG.Certificates.RatExpr
