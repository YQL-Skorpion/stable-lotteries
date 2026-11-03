import OptimalG.VariationalPositiveScores
import OptimalG.VariationalCapImprovement
import OptimalG.VariationalFinitePerturbation

/-! Finite comparison tools for the cap replacement. -/
namespace OptimalG.Certificates.Control

theorem theta_x_shift_nondecreasing (h k R P A B dx dA : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det (h-dx) k R P)
    (hR : 0 ≤ R) (hs : 0 ≤ dA+theta h k R P A B*dx) :
    theta h k R P A B ≤ theta (h-dx) k R P (A+dA) B := by
  apply sub_nonneg.mp
  rw [theta_x_shift _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  exact mul_nonneg (div_nonneg hR hD'.le) hs

theorem theta_y_shift_nondecreasing (h k R P A B dy dB : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det h (k+dy) R P)
    (hP : 0 ≤ P) (hs : 0 ≤ dB+theta h k R P A B*dy) :
    theta h k R P A B ≤ theta h (k+dy) R P A (B+dB) := by
  apply sub_nonneg.mp
  rw [theta_y_shift _ _ _ _ _ _ _ _ hD.ne' hD'.ne']
  exact mul_nonneg (div_nonneg hP hD'.le) hs

theorem value_R_decrease_nonincreasing (U h k R R' P K A B : ℝ)
    (hD : 0 < det h k R P) (hD' : 0 < det h k R' P)
    (hR : R' ≤ R) (ha : 0 ≤ alphaNumerator h k A B) (hc : 0 ≤ cy U h P K) :
    value U h k R' P K A B ≤ value U h k R P K A B := by
  have hh := value_RP_difference U h k R P K A B (R'-R) 0 hD.ne'
    (by simpa only [add_sub_cancel,add_zero] using hD'.ne')
  simp only [add_sub_cancel,add_zero,mul_zero,sub_zero] at hh
  apply sub_nonpos.mp
  rw [hh]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos ha (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hR)))
    (mul_pos hD hD').le

end OptimalG.Certificates.Control

namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem Admissible.cap_coordinate_theta_lower {lam A B : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : A = capScore lam d.S c.2.1 ∨ B = capScore lam d.S c.2.2) :
    (14:ℝ)/100 < featureTheta lam d (c,A,B) := by
  have hR := hd.control_R_lower hc.1
  have hP := Certificates.Compact.complementary_primitive_floor lam d.S c.1
    hd.compact_lambdaRange hd.compact_scalarRange
    (by have hp := hc.1; norm_num [pLo,pHi] at hp ⊢; exact hp)
  have hP0 : 0 ≤ quadratic lam (1-c.1)-d.S := by exact (hd.control_P_bounds hc.1).1
  have hR0 : 0 < primitive lam d c.1 := by linarith
  have hD : 0 < controlDeterminant lam d c := by linarith [hd.determinant_positive hc]
  have hDu := hd.determinant_coarse_upper hc
  have hxc : c.2.1 ∈ Icc ell tEnd :=
    ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans hc.2.1.1,
      hc.2.1.2.trans (by norm_num [xHi,tEnd])⟩
  have hyc : c.2.2 ∈ Icc ell tEnd :=
    ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans ((le_max_left _ _).trans hc.2.2.1),
      hc.2.2.2.trans (by norm_num [xHi,tEnd])⟩
  unfold featureTheta Certificates.Control.theta
  change (14:ℝ)/100 < (primitive lam d c.1*A+(quadratic lam (1-c.1)-d.S)*B)/controlDeterminant lam d c
  apply (lt_div_iff₀ hD).mpr
  rcases hcap with hcap | hcap
  · have hscore := hd.capScore_gt_small hxc
    rw [← hcap] at hscore
    have hm := mul_lt_mul_of_pos_left hscore hR0
    have hn := mul_nonneg hP0 hB
    nlinarith only [hR,hm,hn,hDu]
  · have hscore := hd.capScore_gt_small hyc
    rw [← hcap] at hscore
    have hP' : (11:ℝ)/100 < quadratic lam (1-c.1)-d.S := by
      change (0.113:ℝ) < quadratic lam (1-c.1)-d.S at hP
      norm_num at hP
      linarith
    have hm := mul_lt_mul_of_pos_left hscore (by linarith : 0 < quadratic lam (1-c.1)-d.S)
    have hn := mul_nonneg hR0.le hA
    nlinarith only [hP',hm,hn,hDu]

theorem Admissible.feature_alpha_positive {lam z u A B : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {c : Control} (hc : c ∈ controlDomain)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    (hA : A ≤ lam-c.2.1) (hB : B ≤ lam-c.2.2)
    (hv : featureH hd z u (c,A,B) ≤ lam-z) :
    0 < Certificates.Control.alphaNumerator (2*lam-c.2.1) (c.1+c.2.2-lam) A B := by
  rw [featureH_eq_value hd z u A B hc] at hv
  have hD : 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) := by
    change 0 < controlDeterminant lam d c
    linarith [hd.determinant_positive hc]
  have hgap := Certificates.Control.score_gap lam c.1 c.2.1 c.2.2 (primitive lam d c.1) (quadratic lam (1-c.1)-d.S) A B
    (by linarith [hd.control_R_lower hc.1]) (hd.control_P_bounds hc.1).1 hA hB
    (by linarith [hd.control_binary_gap hc])
  apply Certificates.Control.active_alpha_positive (z-lam) _ _ _ _ _ A B _ hD
    (hd.control_K_bounds hc.1 hz huLow huHigh).1 hgap
  · simpa only [neg_sub] using hv
  · have hz0 := hz.1
    have hl := hd.1.2
    norm_num [zStart,lambdaHi] at hz0 hl
    linarith

end OptimalG.Variational
