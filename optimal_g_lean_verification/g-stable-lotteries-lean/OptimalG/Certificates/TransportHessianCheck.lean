import OptimalG.Certificates.TransportFrozenExpressions
import OptimalG.Certificates.IntegerExpression
import OptimalG.Certificates.SchurCertificate

/-! Integer interval checks of the actual frozen-reference Hessian expressions.
The six coordinates use the symmetric ordering SS,Sr,Sa,rr,ra,aa. -/
namespace OptimalG.Certificates.Transport
open RatExpr
namespace FrozenParameters

def hessianExpressions (d : FrozenParameters) (late : Bool) : Fin 6→E :=
  ![d.hessianEntry late 0 0,
    (d.hessianEntry late 0 1+d.hessianEntry late 1 0)/2,
    (d.hessianEntry late 0 2+d.hessianEntry late 2 0)/2,
    d.hessianEntry late 1 1,
    (d.hessianEntry late 1 2+d.hessianEntry late 2 1)/2,
    d.hessianEntry late 2 2]

def hessianBounds (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) : Option (Fin 6→IntegerInterval) := do
  let b0←(d.hessianExpressions late 0).integerInterval scale box
  let b1←(d.hessianExpressions late 1).integerInterval scale box
  let b2←(d.hessianExpressions late 2).integerInterval scale box
  let b3←(d.hessianExpressions late 3).integerInterval scale box
  let b4←(d.hessianExpressions late 4).integerInterval scale box
  let b5←(d.hessianExpressions late 5).integerInterval scale box
  return ![b0,b1,b2,b3,b4,b5]

theorem hessianBounds_sound {scale : ℕ} (hs : 0<scale) {d : FrozenParameters} {late : Bool}
    {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {bounds : Fin 6→IntegerInterval} (hc : hessianBounds scale d late box=some bounds) :
    ∀ i,(bounds i).Contains scale ((d.hessianExpressions late i).eval x) := by
  unfold hessianBounds at hc
  cases h0 : (d.hessianExpressions late 0).integerInterval scale box with
  | none => simp [h0] at hc
  | some b0 =>
    cases h1 : (d.hessianExpressions late 1).integerInterval scale box with
    | none => simp [h0,h1] at hc
    | some b1 =>
      cases h2 : (d.hessianExpressions late 2).integerInterval scale box with
      | none => simp [h0,h1,h2] at hc
      | some b2 =>
        cases h3 : (d.hessianExpressions late 3).integerInterval scale box with
        | none => simp [h0,h1,h2,h3] at hc
        | some b3 =>
          cases h4 : (d.hessianExpressions late 4).integerInterval scale box with
          | none => simp [h0,h1,h2,h3,h4] at hc
          | some b4 =>
            cases h5 : (d.hessianExpressions late 5).integerInterval scale box with
            | none => simp [h0,h1,h2,h3,h4,h5] at hc
            | some b5 =>
              simp [h0,h1,h2,h3,h4,h5] at hc
              subst bounds
              intro i
              fin_cases i <;> simpa using integerInterval_sound hs box x hx _ (by assumption)

def hessianCheck (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) (rankPenalty scalarLower : ℚ) : Bool :=
  match d.hessianBounds scale late box with
  | none => false
  | some b =>
    (SchurCertificate.d1 rankPenalty).integerLowerCheck scale b 0 &&
      ((SchurCertificate.d2 rankPenalty).integerLowerCheck scale b 0 &&
        (SchurCertificate.schur rankPenalty).integerLowerCheck scale b
          (IntegerInterval.pointRounded scale scalarLower).hi)

theorem hessianCheck_sound {scale : ℕ} (hs : 0<scale) {d : FrozenParameters} {late : Bool}
    {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {rankPenalty scalarLower : ℚ} (hc : d.hessianCheck scale late box rankPenalty scalarLower=true)
    (s r a : ℝ) :
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2)≤
      (d.hessianExpressions late 0).eval x*s^2+2*(d.hessianExpressions late 1).eval x*s*r+
      2*(d.hessianExpressions late 2).eval x*s*a+(d.hessianExpressions late 3).eval x*r^2+
      2*(d.hessianExpressions late 4).eval x*r*a+(d.hessianExpressions late 5).eval x*a^2 := by
  cases hb : d.hessianBounds scale late box with
  | none => simp [hessianCheck,hb] at hc
  | some b =>
    simp only [hessianCheck,hb] at hc
    have h := Bool.and_eq_true_iff.mp hc
    have h' := Bool.and_eq_true_iff.mp h.2
    let values : Fin 6→ℝ := fun i => (d.hessianExpressions late i).eval x
    have hv : ∀ i,(b i).Contains scale (values i) := hessianBounds_sound hs hx hb
    have h1 := integerLowerCheck_sound hs (SchurCertificate.d1 rankPenalty) b 0 h.1 values hv
    have h2 := integerLowerCheck_sound hs (SchurCertificate.d2 rankPenalty) b 0 h'.1 values hv
    have h3 := integerLowerCheck_sound hs (SchurCertificate.schur rankPenalty) b
      (IntegerInterval.pointRounded scale scalarLower).hi h'.2 values hv
    have htarget := IntegerInterval.upper_bound hs (IntegerInterval.pointRounded_contains scale scalarLower)
    have hscalar := htarget.trans h3.le
    simp only [SchurCertificate.d1,SchurCertificate.d2,SchurCertificate.schur,
      eval_addNotation,eval_subNotation,eval_mulNotation,eval_divNotation,eval,
      Int.cast_zero,zero_div] at h1 h2 hscalar
    apply schur_quadratic_lower h1
    · simpa only [pow_two,div_eq_mul_inv] using h2
    · simpa only [pow_two,div_eq_mul_inv] using hscalar

end FrozenParameters
end OptimalG.Certificates.Transport
