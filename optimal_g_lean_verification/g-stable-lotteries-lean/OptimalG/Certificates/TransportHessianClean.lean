import OptimalG.Certificates.TransportHessianValidity
import OptimalG.Certificates.ExpressionCleanup
import OptimalG.Certificates.IntegerExpression
import OptimalG.Certificates.SchurCertificate

/-! The same actual Hessian bounds with value-preserving expression cleanup.
Original logarithmic factors are checked separately for regularity below. -/
namespace OptimalG.Certificates.Transport
open RatExpr
namespace FrozenParameters

def originalNonzeroCheck (scale : ℕ) (box : Fin 16→IntegerInterval) (e : E) : Bool :=
  match e.integerInterval scale box with
  | none => false
  | some b => decide (b.hi<0 ∨ 0<b.lo)

theorem originalNonzeroCheck_sound {scale : ℕ} (hs : 0<scale)
    {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {e : E} (hc : originalNonzeroCheck scale box e=true) : e.Valid x ∧ e.eval x≠0 := by
  cases hb : e.integerInterval scale box with
  | none => simp [originalNonzeroCheck,hb] at hc
  | some b =>
    have hh : b.hi<0 ∨ 0<b.lo := by simpa only [originalNonzeroCheck,hb,decide_eq_true_eq] using hc
    refine ⟨integerInterval_valid hs box x hx e hb,?_⟩
    have hval := integerInterval_sound hs box x hx e hb
    intro hz
    rw [hz] at hval
    simp only [IntegerInterval.Contains,mul_zero] at hval
    rcases hh with hneg | hpos
    · have hh' : (b.hi:ℝ)<0 := by exact_mod_cast hneg
      linarith [hval.2]
    · have hh' : (0:ℝ)<b.lo := by exact_mod_cast hpos
      linarith [hval.1]

def originalSourceCheck (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) (i : Fin 4) : Bool :=
  originalNonzeroCheck scale box d.j &&
    (originalNonzeroCheck scale box (d.numerators late i) &&
      (originalNonzeroCheck scale box (d.score i) &&
        originalNonzeroCheck scale box (d.denominator late)))

def originalRegularCheck (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) : Bool :=
  (if late then List.finRange 4 else [1,3]).all (d.originalSourceCheck scale late box)

theorem originalRegularCheck_sound {scale : ℕ} (hs : 0<scale)
    {d : FrozenParameters} {late : Bool} {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ}
    (hx : ∀ i,(box i).Contains scale (x i))
    (hc : d.originalRegularCheck scale late box=true) :
    ∀ i∈activeTerms late,d.sourceRegular late i x := by
  intro i hi
  have hmem : i∈(if late then List.finRange 4 else [1,3]) := by
    cases late <;> simp_all [activeTerms]
  have hh := List.all_eq_true.mp hc i hmem
  have hparts := Bool.and_eq_true_iff.mp hh
  have hrest := Bool.and_eq_true_iff.mp hparts.2
  have hend := Bool.and_eq_true_iff.mp hrest.2
  have hj := originalNonzeroCheck_sound hs hx hparts.1
  have hN := originalNonzeroCheck_sound hs hx hrest.1
  have hm := originalNonzeroCheck_sound hs hx hend.1
  have hD := originalNonzeroCheck_sound hs hx hend.2
  exact ⟨hj.1,hj.2,hN.1,hN.2,hm.1,hm.2,hD.1,hD.2⟩

def hessianBoundsClean (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) : Option (Fin 6→IntegerInterval) := do
  let b0←(d.hessianExpressions late 0).cleanup.integerInterval scale box
  let b1←(d.hessianExpressions late 1).cleanup.integerInterval scale box
  let b2←(d.hessianExpressions late 2).cleanup.integerInterval scale box
  let b3←(d.hessianExpressions late 3).cleanup.integerInterval scale box
  let b4←(d.hessianExpressions late 4).cleanup.integerInterval scale box
  let b5←(d.hessianExpressions late 5).cleanup.integerInterval scale box
  return ![b0,b1,b2,b3,b4,b5]

theorem hessianBoundsClean_sound {scale : ℕ} (hs : 0<scale) {d : FrozenParameters} {late : Bool}
    {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {bounds : Fin 6→IntegerInterval} (hc : hessianBoundsClean scale d late box=some bounds) :
    ∀ i,(bounds i).Contains scale ((d.hessianExpressions late i).eval x) := by
  unfold hessianBoundsClean at hc
  cases h0 : (d.hessianExpressions late 0).cleanup.integerInterval scale box with
  | none => simp [h0] at hc
  | some b0 =>
    cases h1 : (d.hessianExpressions late 1).cleanup.integerInterval scale box with
    | none => simp [h0,h1] at hc
    | some b1 =>
      cases h2 : (d.hessianExpressions late 2).cleanup.integerInterval scale box with
      | none => simp [h0,h1,h2] at hc
      | some b2 =>
        cases h3 : (d.hessianExpressions late 3).cleanup.integerInterval scale box with
        | none => simp [h0,h1,h2,h3] at hc
        | some b3 =>
          cases h4 : (d.hessianExpressions late 4).cleanup.integerInterval scale box with
          | none => simp [h0,h1,h2,h3,h4] at hc
          | some b4 =>
            cases h5 : (d.hessianExpressions late 5).cleanup.integerInterval scale box with
            | none => simp [h0,h1,h2,h3,h4,h5] at hc
            | some b5 =>
              simp [h0,h1,h2,h3,h4,h5] at hc
              subst bounds
              intro i
              fin_cases i <;> simpa using integerInterval_cleanup_sound hs box x hx _ (by assumption)

def hessianCleanArithmeticCheck (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) (rankPenalty scalarLower : ℚ) : Bool :=
  match d.hessianBoundsClean scale late box with
  | none => false
  | some b =>
    (SchurCertificate.d1 rankPenalty).integerLowerCheck scale b 0 &&
      ((SchurCertificate.d2 rankPenalty).integerLowerCheck scale b 0 &&
        (SchurCertificate.schur rankPenalty).integerLowerCheck scale b
          (IntegerInterval.pointRounded scale scalarLower).hi)

theorem hessianCleanArithmeticCheck_sound {scale : ℕ} (hs : 0<scale) {d : FrozenParameters} {late : Bool}
    {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ} (hx : ∀ i,(box i).Contains scale (x i))
    {rankPenalty scalarLower : ℚ} (hc : d.hessianCleanArithmeticCheck scale late box rankPenalty scalarLower=true)
    (s r a : ℝ) :
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2)≤
      (d.hessianExpressions late 0).eval x*s^2+2*(d.hessianExpressions late 1).eval x*s*r+
      2*(d.hessianExpressions late 2).eval x*s*a+(d.hessianExpressions late 3).eval x*r^2+
      2*(d.hessianExpressions late 4).eval x*r*a+(d.hessianExpressions late 5).eval x*a^2 := by
  cases hb : d.hessianBoundsClean scale late box with
  | none => simp [hessianCleanArithmeticCheck,hb] at hc
  | some b =>
    simp only [hessianCleanArithmeticCheck,hb] at hc
    have h := Bool.and_eq_true_iff.mp hc
    have h' := Bool.and_eq_true_iff.mp h.2
    let values : Fin 6→ℝ := fun i => (d.hessianExpressions late i).eval x
    have hv : ∀ i,(b i).Contains scale (values i) := hessianBoundsClean_sound hs hx hb
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

def hessianCleanCheck (scale : ℕ) (d : FrozenParameters) (late : Bool)
    (box : Fin 16→IntegerInterval) (rankPenalty scalarLower : ℚ) : Bool :=
  d.originalRegularCheck scale late box &&
    d.hessianCleanArithmeticCheck scale late box rankPenalty scalarLower

theorem hessianCleanCheck_sourceRegular {scale : ℕ} (hs : 0<scale)
    {d : FrozenParameters} {late : Bool} {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ}
    (hx : ∀ i,(box i).Contains scale (x i)) {rankPenalty scalarLower : ℚ}
    (hc : d.hessianCleanCheck scale late box rankPenalty scalarLower=true) :
    ∀ i∈activeTerms late,d.sourceRegular late i x :=
  originalRegularCheck_sound hs hx (Bool.and_eq_true_iff.mp hc).1

theorem hessianCleanCheck_sound {scale : ℕ} (hs : 0<scale)
    {d : FrozenParameters} {late : Bool} {box : Fin 16→IntegerInterval} {x : Fin 16→ℝ}
    (hx : ∀ i,(box i).Contains scale (x i)) {rankPenalty scalarLower : ℚ}
    (hc : d.hessianCleanCheck scale late box rankPenalty scalarLower=true) (s r a : ℝ) :
    (scalarLower:ℝ)*s^2-(rankPenalty:ℝ)*(r^2+a^2)≤d.checkedQuadratic late x s r a :=
  hessianCleanArithmeticCheck_sound hs hx (Bool.and_eq_true_iff.mp hc).2 s r a

end FrozenParameters
end OptimalG.Certificates.Transport
