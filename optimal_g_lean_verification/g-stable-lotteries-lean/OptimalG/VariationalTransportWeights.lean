import OptimalG.VariationalTransportEntropy

/-! Scalar reciprocal-derivative and weighted entropy estimates for Appendix B.4.
These lemmas do not assume existence of a matched-rank map or a reference
certificate: they supply the inequalities subsequently integrated along it. -/
namespace OptimalG.Variational
open Real

 theorem transportEntropy_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ transportEntropy x := by
  exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos hx)

 theorem reciprocal_exp_entropy {x v : ℝ} (hx : 0 < x) :
    transportEntropy x ≤ Real.exp v / x - 1 - v + x - 1 := by
  have h := Real.add_one_le_exp (v-Real.log x)
  rw [Real.exp_sub,Real.exp_log hx] at h
  unfold transportEntropy
  linarith

 theorem reciprocal_exp_coercive {x v : ℝ} (hx : 0 < x) :
    (8:ℝ)/9*(x-1)^2/(x+1) ≤ Real.exp v / x - 1 - v + x - 1 :=
  (transportEntropy_coercive hx).trans (reciprocal_exp_entropy hx)

/-- The two-entropy identity remains valid without approximation. -/
theorem weighted_entropy_identity {a w x : ℝ} (ha : 0 < a) (hw : 0 < w) (hx : 0 < x) :
    w*transportEntropy x+(a-w)*(x-1) =
      w*transportEntropy (a*x/w)+w*transportEntropy (w/a)-(a-w)^2/a := by
  unfold transportEntropy
  rw [Real.log_div (mul_pos ha hx).ne' hw.ne',Real.log_mul ha.ne' hx.ne',
    Real.log_div hw.ne' ha.ne']
  field_simp
  ring

/-- The residual linear variation is absorbed by a squared stationarity error. -/
theorem weighted_entropy_absorption {a w x : ℝ} (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x) :
    -(a-w)^2/a ≤ w*transportEntropy x+(a-w)*(x-1) := by
  rcases hw.eq_or_lt with hw0 | hwp
  · rw [← hw0]
    have he : -(a-0)^2/a = -a := by field_simp; ring
    rw [he]
    nlinarith only [mul_pos ha hx]
  · rw [weighted_entropy_identity ha hwp hx]
    have h1 := mul_nonneg hw (transportEntropy_nonneg (div_pos (mul_pos ha hx) hwp))
    have h2 := mul_nonneg hw (transportEntropy_nonneg (div_pos hwp ha))
    simpa only [zero_sub,neg_div] using sub_le_sub_right (add_nonneg h1 h2) ((a-w)^2/a)

/-- Pointwise form of the main absorption step in (B.11). Here P is the
integrated rank derivative P₁, W is the pushed-forward positive ODE weight,
and k is the constant whose boundary contribution is retained separately. -/
theorem transport_weight_coercivity {P W W0 k x : ℝ}
    (hW0 : 0 ≤ W0) (hW : W0 ≤ W) (ha : 0 < P-k-W0) (hx : 0 < x) :
    (8:ℝ)/9*W0*((x-1)^2/(x+1))-(P-W-k)^2/(P-k-W0) ≤
      (P-W-k)*(x-1)+W*transportEntropy x := by
  have hco := mul_le_mul_of_nonneg_left (transportEntropy_coercive hx) hW0
  have habs := weighted_entropy_absorption ha (sub_nonneg.mpr hW) hx
  have he : (P-k-W0)-(W-W0) = P-W-k := by ring
  rw [he] at habs
  convert! (add_le_add hco habs) using 1 <;> ring

/-- Completion of the scalar slack square, with an inexact first derivative. -/
theorem slack_square_completion {A A0 kappa s : ℝ}
    (hk : 0 < kappa) (hA : |A| ≤ A0) :
    -(A0^2/(4*kappa)) ≤ A*s+kappa*s^2 := by
  have hA0 : 0 ≤ A0 := (abs_nonneg A).trans hA
  have hAsq : A^2 ≤ A0^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg A) hA0).2 hA
  have hsq := sq_nonneg (2*kappa*s+A)
  rw [← neg_div]
  apply (div_le_iff₀ (show 0 < 4*kappa by positivity)).2
  nlinarith

end OptimalG.Variational
