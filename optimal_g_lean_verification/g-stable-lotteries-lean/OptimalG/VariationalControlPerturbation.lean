import OptimalG.ParameterTransferField

/-! Quantitative control perturbation estimates for the reverse comparison
needed when transferring localization back to the original parameter. -/
namespace OptimalG.Variational
open Set MeasureTheory

 theorem abs_mul_change {a b a' b' ea eb A B : ℝ}
    (hea : |a'-a| ≤ ea) (heb : |b'-b| ≤ eb)
    (ha : |a| ≤ A) (hb : |b'| ≤ B) (hea0 : 0 ≤ ea) (hB : 0 ≤ B) :
    |a'*b'-a*b| ≤ ea*B+A*eb := by
  have he : a'*b'-a*b=(a'-a)*b'+a*(b'-b) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  exact add_le_add (mul_le_mul hea hb (abs_nonneg _) hea0)
    (mul_le_mul ha heb (abs_nonneg _) (le_trans (abs_nonneg _) ha))

 theorem rational_control_perturbation {N N' D D' delta : ℝ}
    (hd : 0 ≤ delta) (hD : (0.0519 : ℝ) ≤ D) (hD' : (0.0519 : ℝ) ≤ D')
    (hN : |N| ≤ 0.063) (hNd : |N'-N| ≤ 0.7*delta)
    (hDd : |D'-D| ≤ 1.5*delta) : |(-N'/D')-(-N/D)| ≤ 50*delta := by
  have hDp : 0 < D := by linarith
  have hD'p : 0 < D' := by linarith
  have hDD : (0.0519 : ℝ)^2 ≤ D*D' := by
    simpa only [pow_two] using mul_le_mul hD hD' (by norm_num) hDp.le
  have he : (-N'/D')-(-N/D)= -(N'-N)/D'+N*(D'-D)/(D*D') := by
    field_simp [ne_of_gt hDp,ne_of_gt hD'p]
    <;> ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_div,abs_neg,abs_mul,abs_of_pos hD'p,abs_of_pos (mul_pos hDp hD'p)]
  have h1 : |N'-N| / D' ≤ (0.7*delta)/0.0519 :=
    div_le_div₀ (by positivity) hNd (by norm_num) hD'
  have hn : |N| * |D'-D| ≤ 0.063*(1.5*delta) :=
    mul_le_mul hN hDd (abs_nonneg _) (by norm_num)
  have h2 : |N| * |D'-D| / (D*D') ≤ (0.063*(1.5*delta))/(0.0519^2) :=
    div_le_div₀ (by positivity) hn (by norm_num) hDD
  apply (add_le_add h1 h2).trans
  norm_num [div_eq_mul_inv]
  nlinarith only [hd]

 theorem control_numerator_perturbation {U U' K K' C C' E E' delta : ℝ}
    (hd : 0 ≤ delta)
    (hU : |U| ≤ 0.334) (hK : |K| ≤ 0.12)
    (hC' : |C'| ≤ 0.084) (hE' : |E'| ≤ 0.287)
    (hUd : |U'-U| ≤ delta) (hKd : |K'-K| ≤ delta)
    (hCd : |C'-C| ≤ 0.556*delta) (hEd : |E'-E| ≤ 0.834*delta) :
    |(U'*C'+K'*E')-(U*C+K*E)| ≤ 0.7*delta := by
  have h1 := abs_mul_change hUd hCd hU hC' hd (by norm_num : (0 : ℝ) ≤ 0.084)
  have h2 := abs_mul_change hKd hEd hK hE' hd (by norm_num : (0 : ℝ) ≤ 0.287)
  have he : (U'*C'+K'*E')-(U*C+K*E)=(U'*C'-U*C)+(K'*E'-K*E) := by ring
  rw [he]
  have hh := abs_add_le (U'*C'-U*C) (K'*E'-K*E)
  nlinarith only [hh,h1,h2,hd]

 theorem control_denominator_perturbation {h h' k k' R R' P P' delta : ℝ}
    (hd : 0 ≤ delta) (hh : |h| ≤ 0.85) (hk : |k| ≤ 0.18)
    (hR' : |R'| ≤ 0.14) (hP' : |P'| ≤ 0.16)
    (hhd : |h'-h| ≤ 2*delta) (hkd : |k'-k| ≤ delta)
    (hRd : |R'-R| ≤ delta) (hPd : |P'-P| ≤ delta) :
    |(h'*R'-k'*P')-(h*R-k*P)| ≤ 1.5*delta := by
  have h1 := abs_mul_change hhd hRd hh hR' (by positivity) (by norm_num : (0 : ℝ) ≤ 0.14)
  have h2 := abs_mul_change hkd hPd hk hP' hd (by norm_num : (0 : ℝ) ≤ 0.16)
  have he : (h'*R'-k'*P')-(h*R-k*P)=(h'*R'-h*R)-(k'*P'-k*P) := by ring
  rw [he]
  have hh := abs_add_le (h'*R'-h*R) (-(k'*P'-k*P))
  rw [abs_neg,← sub_eq_add_neg] at hh
  nlinarith only [hh,h1,h2,hd]

 theorem score_linear_bound {a b A B : ℝ} {ca cb : ℝ}
    (ha : |a| ≤ ca) (hb : |b| ≤ cb) (hA : |A| ≤ 0.278) (hB : |B| ≤ 0.278)
    (hca : 0 ≤ ca) (hcb : 0 ≤ cb) : |a*A+b*B| ≤ (ca+cb)*0.278 := by
  have h1 := mul_le_mul ha hA (abs_nonneg _) hca
  have h2 := mul_le_mul hb hB (abs_nonneg _) hcb
  have hh := abs_add_le (a*A) (b*B)
  rw [abs_mul,abs_mul] at hh
  nlinarith only [h1,h2,hh]

 theorem score_linear_change {a b a' b' A B : ℝ} {ca cb : ℝ}
    (ha : |a'-a| ≤ ca) (hb : |b'-b| ≤ cb) (hA : |A| ≤ 0.278) (hB : |B| ≤ 0.278)
    (hca : 0 ≤ ca) (hcb : 0 ≤ cb) :
    |(a'*A+b'*B)-(a*A+b*B)| ≤ (ca+cb)*0.278 := by
  have he : (a'*A+b'*B)-(a*A+b*B)=(a'-a)*A+(b'-b)*B := by ring
  rw [he]
  exact score_linear_bound ha hb hA hB hca hcb

 theorem finite_control_perturbation {U U' h h' k k' R R' P P' K K' A B delta : ℝ}
    (hd : 0 ≤ delta) (hU : |U| ≤ 0.334) (hK : |K| ≤ 0.12)
    (hh : |h| ≤ 0.85) (hh' : |h'| ≤ 0.85) (hk : |k| ≤ 0.18) (hk' : |k'| ≤ 0.18)
    (hR : |R| ≤ 0.14) (hR' : |R'| ≤ 0.14) (hP : |P| ≤ 0.16) (hP' : |P'| ≤ 0.16)
    (hA : |A| ≤ 0.278) (hB : |B| ≤ 0.278)
    (hUd : |U'-U| ≤ delta) (hKd : |K'-K| ≤ delta)
    (hhd : |h'-h| ≤ 2*delta) (hkd : |k'-k| ≤ delta)
    (hRd : |R'-R| ≤ delta) (hPd : |P'-P| ≤ delta)
    (hD : (0.0519 : ℝ) ≤ h*R-k*P) (hD' : (0.0519 : ℝ) ≤ h'*R'-k'*P') :
    |Certificates.Control.value U' h' k' R' P' K' A B-
      Certificates.Control.value U h k R P K A B| ≤ 50*delta := by
  have hC : |R*A+P*B| ≤ (0.084 : ℝ) :=
    (score_linear_bound hR hP hA hB (by norm_num) (by norm_num)).trans (by norm_num)
  have hC' : |R'*A+P'*B| ≤ (0.084 : ℝ) :=
    (score_linear_bound hR' hP' hA hB (by norm_num) (by norm_num)).trans (by norm_num)
  have hE : |k*A+h*B| ≤ (0.287 : ℝ) :=
    (score_linear_bound hk hh hA hB (by norm_num) (by norm_num)).trans (by norm_num)
  have hE' : |k'*A+h'*B| ≤ (0.287 : ℝ) :=
    (score_linear_bound hk' hh' hA hB (by norm_num) (by norm_num)).trans (by norm_num)
  have hCd : |(R'*A+P'*B)-(R*A+P*B)| ≤ 0.556*delta := by
    have hi := score_linear_change hRd hPd hA hB hd hd
    nlinarith only [hi]
  have hEd : |(k'*A+h'*B)-(k*A+h*B)| ≤ 0.834*delta := by
    have hi := score_linear_change hkd hhd hA hB hd (by positivity)
    nlinarith only [hi]
  have hN : |U*(R*A+P*B)+K*(k*A+h*B)| ≤ (0.063 : ℝ) := by
    have h1 := mul_le_mul hU hC (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.334)
    have h2 := mul_le_mul hK hE (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 0.12)
    have hi := abs_add_le (U*(R*A+P*B)) (K*(k*A+h*B))
    rw [abs_mul,abs_mul] at hi
    linarith
  have hi := rational_control_perturbation hd hD hD' hN
    (control_numerator_perturbation hd hU hK hC' hE' hUd hKd hCd hEd)
    (control_denominator_perturbation hd hh hk hR' hP' hhd hkd hRd hPd)
  simpa only [Certificates.Control.value,Certificates.Control.det,
    Certificates.Control.alphaNumerator] using hi

end OptimalG.Variational
