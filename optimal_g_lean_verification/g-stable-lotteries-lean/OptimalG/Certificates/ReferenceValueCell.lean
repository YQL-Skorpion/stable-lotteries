import OptimalG.Certificates.ReferenceFlowExpressions
import OptimalG.Certificates.IntegerEnclosures

/-! A reference-deficit interval encloses the actual affine solution through
its proved error from the local cubic, rather than assuming the cubic exact. -/
namespace OptimalG.Certificates.Transport.ReferenceFlowCell
open Set RatExpr

def valueWithErrorExpr (c : ReferenceFlowCell) : RatExpr 2 :=
  RatExpr.polynomial c.valuePolynomial (.var 0)+.var 1

def valueErrorRadius (c : ReferenceFlowCell) (start : ℚ) : ℚ :=
  (c.segment.right.z-start)/2500000000

def actualValueCheck (s k : ℕ) (c : ReferenceFlowCell) (start : ℚ)
    (out : IntegerInterval) : Bool :=
  (valueWithErrorExpr c).enclosureCheck (k*s)
    ![⟨0,(k*s:ℕ)⟩,IntegerInterval.fromRat (k*s)
      ⟨-c.valueErrorRadius start,c.valueErrorRadius start⟩] (out.rescale k)

theorem actualValueCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceFlowCell) (start : ℚ) (out : IntegerInterval)
    (hc : c.actualValueCheck s k start out=true) {t Z : ℝ}
    (ht : t∈Icc (0:ℝ) 1)
    (herror : |Z-c.valuePolynomial.eval t|≤(c.valueErrorRadius start:ℝ)) :
    out.Contains s Z := by
  have hunit : (⟨0,((k*s:ℕ):ℤ)⟩:IntegerInterval).Contains (k*s) t := by
    constructor
    · simpa using (mul_nonneg (show (0:ℝ)≤(k*s:ℕ) by positivity) ht.1)
    · simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (k*s))
  have hE : (IntegerInterval.fromRat (k*s)
      ⟨-c.valueErrorRadius start,c.valueErrorRadius start⟩).Contains (k*s)
      (Z-c.valuePolynomial.eval t) := by
    apply IntegerInterval.fromRat_contains (Nat.mul_pos hk hs)
    simpa only [RatInterval.Contains,Rat.cast_neg] using abs_le.mp herror
  have hx : ∀ i,(![⟨0,((k*s:ℕ):ℤ)⟩,IntegerInterval.fromRat (k*s)
      ⟨-c.valueErrorRadius start,c.valueErrorRadius start⟩] i).Contains (k*s)
      (![t,Z-c.valuePolynomial.eval t] i) := by
    intro i
    fin_cases i
    · simpa using hunit
    · simpa using hE
  have he := RatExpr.enclosureCheck_sound (Nat.mul_pos hk hs)
    (valueWithErrorExpr c) _ (out.rescale k) hc _ hx
  have hvalue : (valueWithErrorExpr c).eval ![t,Z-c.valuePolynomial.eval t]=Z := by
    simp [valueWithErrorExpr,eval_addNotation,polynomial_eval,eval]
  rw [hvalue] at he
  exact (IntegerInterval.rescale_contains_iff hk s out Z).mp he

/-- A global residual enclosure specializes to the error radius advertised
by a local time cell. -/
theorem valueErrorRadius_of_global {c : ReferenceFlowCell} {start : ℚ} {z Z X : ℝ}
    (hz : z≤(c.segment.right.z:ℝ))
    (herror : |Z-X|≤(z-start)/2500000000) :
    |Z-X|≤(c.valueErrorRadius start:ℝ) := by
  have h := div_le_div_of_nonneg_right (sub_le_sub_right hz (start:ℝ))
    (by norm_num : (0:ℝ)≤2500000000)
  exact herror.trans (by simpa [valueErrorRadius] using h)

end OptimalG.Certificates.Transport.ReferenceFlowCell
