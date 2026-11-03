import OptimalG.Certificates.ReferenceValueCell

/-! Explicit error-radius enclosures for actual reference values. -/
namespace OptimalG.Certificates.Transport.ReferenceFlowCell
open Set RatExpr

def actualValueCheckWithError (s k : ℕ) (c : ReferenceFlowCell) (error : ℚ)
    (out : IntegerInterval) : Bool :=
  (valueWithErrorExpr c).enclosureCheck (k*s)
    ![⟨0,(k*s:ℕ)⟩,IntegerInterval.fromRat (k*s)
      ⟨-error,error⟩] (out.rescale k)

theorem actualValueCheckWithError_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceFlowCell) (error : ℚ) (out : IntegerInterval)
    (hc : c.actualValueCheckWithError s k error out=true) {t Z : ℝ}
    (ht : t∈Icc (0:ℝ) 1)
    (herror : |Z-c.valuePolynomial.eval t|≤(error:ℝ)) :
    out.Contains s Z := by
  have hunit : (⟨0,((k*s:ℕ):ℤ)⟩:IntegerInterval).Contains (k*s) t := by
    constructor
    · simpa using (mul_nonneg (show (0:ℝ)≤(k*s:ℕ) by positivity) ht.1)
    · simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg (k*s))
  have hE : (IntegerInterval.fromRat (k*s)
      ⟨-error,error⟩).Contains (k*s)
      (Z-c.valuePolynomial.eval t) := by
    apply IntegerInterval.fromRat_contains (Nat.mul_pos hk hs)
    simpa only [RatInterval.Contains,Rat.cast_neg] using abs_le.mp herror
  have hx : ∀ i,(![⟨0,((k*s:ℕ):ℤ)⟩,IntegerInterval.fromRat (k*s)
      ⟨-error,error⟩] i).Contains (k*s)
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

/-- Restrict any nonnegative linear global error rate to a time cell. -/
theorem error_radius_on_cell {c : ReferenceFlowCell} {start rate : ℚ} {z Z X : ℝ}
    (hrate : 0≤rate) (hz : z≤(c.segment.right.z:ℝ))
    (herror : |Z-X|≤(rate:ℝ)*(z-start)) :
    |Z-X|≤((rate*(c.segment.right.z-start):ℚ):ℝ) := by
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hz (start:ℝ))
    (show (0:ℝ)≤rate by exact_mod_cast hrate)
  exact herror.trans (by simpa only [Rat.cast_mul,Rat.cast_sub] using hh)

end OptimalG.Certificates.Transport.ReferenceFlowCell
