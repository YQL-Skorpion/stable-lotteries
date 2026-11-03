import OptimalG.Certificates.VariationalSplitGapData
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.VariationalThetaUpper
import OptimalG.VariationalVerifierCoefficients

/-! The variational split margin follows by testing the second support
inequality at the single line rank .36. No optimizing rank is needed. -/
namespace OptimalG.Certificates
open Set SmallMassExpressions

theorem variational_split_numerator_identity {lam S p : ℝ} (hp : p≠1) :
    557430501712500*(1-p)*
      ((p+(11/39)*(lam-9/25))*(initial lam S-lam+391/500-p)-Variational.cap lam S p)=
      VariationalSplitGapData.numerator lam S p := by
  have hd : 1-p≠0 := sub_ne_zero.mpr (Ne.symm hp)
  rw [initial_formula]
  unfold Variational.cap
  field_simp [hd]
  norm_num [VariationalSplitGapData.numerator]
  <;> ring

theorem variational_split_numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (527/2000:ℝ) (9/25)) :
    Variational.cap lam S p <
      (p+(11/39)*(lam-9/25))*(initial lam S-lam+391/500-p) := by
  have hp1 : p<1 := by linarith only [hp.2]
  have hn := VariationalSplitGapData.numerator_pos hL hS hp
  have he := variational_split_numerator_identity (lam:=lam) (S:=S) (ne_of_lt hp1)
  have hfactor : 0 < (557430501712500:ℝ)*(1-p) := by positivity
  have hpos : 0 <
      (p+(11/39)*(lam-9/25))*(initial lam S-lam+391/500-p)-Variational.cap lam S p := by
    apply (mul_pos_iff_of_pos_left hfactor).mp
    rw [he]
    exact hn
  linarith only [hpos]

theorem variational_split_gap {phi : ℝ→ℝ} {lam S p beta eta : ℝ}
    (h : VerifierCurve phi lam)
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (527/2000:ℝ) (9/25))
    (hbeta : 0≤beta) (heta : (50/39:ℝ)≤eta)
    (hzero : phi 0=initial lam S)
    (hline : phi (9/25)=lam-9/25)
    (hcap : curvePrimitive phi p≤Variational.cap lam S p)
    (hsupport : (9/25:ℝ)+eta*phi (9/25)≤lam-p+beta*curvePrimitive phi p) :
    1 < beta*(phi 0-lam+391/500-p) := by
  have hn := variational_split_numerator_pos hL hS hp
  have hf := initial_bounds hL hS
  have hg : 0 < initial lam S-lam+391/500-p := by
    linarith only [hf.1,hL.2,hp.2]
  have hlp : 0≤lam-9/25 := by linarith only [hL.1]
  have hs := mul_le_mul_of_nonneg_right heta hlp
  rw [hline] at hsupport
  have hbetaR : p+(11/39)*(lam-9/25)≤beta*curvePrimitive phi p := by
    linarith only [hs,hsupport]
  have hm := mul_le_mul_of_nonneg_right hbetaR hg.le
  have hR := h.primitive_pos (q:=p) ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  rw [hzero]
  by_contra hnot
  have hsmall := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hR.le
  nlinarith only [hm,hn,hcap,hsmall]

end OptimalG.Certificates
