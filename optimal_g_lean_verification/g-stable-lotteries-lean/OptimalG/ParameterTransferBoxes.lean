import OptimalG.ParameterTransferCap
import OptimalG.VariationalStateBounds

/-! Determinant and binary bounds throughout the explicit upward transfer. -/
namespace OptimalG.Variational.ParameterTransfer
open Set

theorem Admissible_control_R_small {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    primitive lam d p < 0.12 := by
  have hL := h.compact_lambdaRange
  have hs := h.slack_lower
  have hcap := h.control_primitive_cap hp
  have hp' : p ∈ Icc (0.25 : ℝ) 0.36 := by
    convert! hp using 1 <;> norm_num [pLo,pHi]
  have hden : 0 < 1-p := by linarith [hp'.2]
  have hnum : (0.0164 : ℝ)*(1-p) ≤ lam*d.S := by
    have hh := mul_le_mul hL.1 hs (by norm_num : (0 : ℝ) ≤ 21972/1000000)
      (by linarith [hL.1] : 0 ≤ lam)
    nlinarith [hp'.1]
  have hfrac : (0.0164 : ℝ) ≤ lam*d.S/(1-p) := (le_div_iff₀ hden).mpr hnum
  have hsq := mul_nonneg (sub_nonneg.mpr hL.2)
    (show 0 ≤ 0.562330+lam by linarith [hL.1])
  have hmp := mul_le_mul hL.2 hp'.2 (by linarith [hp'.1] : 0 ≤ p) (by norm_num : (0 : ℝ) ≤ 0.562330)
  unfold cap at hcap
  nlinarith [hL.1]

theorem Admissible_complement_binary {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    (1-p)*primitive lam d p ≤ lam*(quadratic lam (1-p)-d.S) := by
  have hp' : p ≤ (0.36 : ℝ) := by
    convert! hp.2 using 1 <;> norm_num [pHi]
  have hcap := h.control_primitive_cap hp
  rw [← certificates_cap,Certificates.cap_eq_quotient lam d.S p (by linarith)] at hcap
  have hh := (le_div_iff₀ (show 0 < 1-p by linarith)).mp hcap
  simpa only [certificates_quadratic,mul_comm] using hh

/-- A finite interpolation rectangle. All products are bounded with exact
rational inequalities, including the two coupled binary conditions. -/
theorem phase_RP_boxes {lam delta p x y R P s : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : delta ∈ Icc (0 : ℝ) 0.000005) (hs : s ∈ Icc (0 : ℝ) delta)
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hx : x ∈ Icc (0.285 : ℝ) 0.38)
    (hy : y ∈ Icc (0.285 : ℝ) 0.38)
    (hR : R ∈ Icc (0.0826 : ℝ) 0.12) (hP : P ∈ Icc (0 : ℝ) 0.159)
    (hD : 0.0519 < (2*lam-x)*R-(p+y-lam)*P)
    (hB : 0.01446 < lam*R-p*P) (hcomp : (1-p)*R ≤ lam*P) :
    let Rt := R+s*0.1788
    let Pt := P+s*(0.7988-p)
    Rt ∈ Icc (0.0826 : ℝ) 0.136 ∧ 0 ≤ Pt ∧
      0.0519 < Certificates.Control.det (2*(lam+delta)-x) (p+y-(lam+delta)) Rt Pt ∧
      0 < (lam+delta)*Rt-p*Pt ∧ (1-p)*Rt ≤ (lam+delta)*Pt := by
  have hsmax : s ≤ (0.000005 : ℝ) := hs.2.trans hd.2
  have hdp : 0 ≤ 0.62-p := by linarith [hp.2]
  have hdeltaD := mul_nonneg hd.1 (show 0 ≤ 2*R+P by linarith [hR.1,hP.1])
  have hkloss := mul_le_mul
    (show p+y-(lam+delta) ≤ 0.178 by linarith [hp.2,hy.2,hLnew.1])
    (show 0.62-p ≤ 0.37 by linarith [hp.1]) hdp (by norm_num : (0 : ℝ) ≤ 0.178)
  have hdetcoef : 0 ≤ (3*(lam+delta)-x-p-y)*0.1788-(p+y-(lam+delta))*(0.62-p) := by
    linarith [hLnew.1,hx.2,hp.2,hy.2]
  have hdetgain := mul_nonneg hs.1 hdetcoef
  have hRg := mul_nonneg hs.1 (by norm_num : (0 : ℝ) ≤ 0.1788)
  have hPg := mul_nonneg hs.1 (show 0 ≤ 0.7988-p by linarith [hp.2])
  have hdeltaB := mul_nonneg hd.1 (show 0 ≤ R by linarith [hR.1])
  have hBg := mul_nonneg hs.1
    (mul_nonneg (show 0 ≤ lam+delta-p by linarith [hLnew.1,hp.2])
      (by norm_num : (0 : ℝ) ≤ 0.1788))
  have hBloss0 := mul_le_mul hp.2 (show 0.62-p ≤ 0.37 by linarith [hp.1])
    hdp (by norm_num : (0 : ℝ) ≤ 0.36)
  have hBloss := mul_le_mul_of_nonneg_left hBloss0 hs.1
  have hcompBase := mul_nonneg hd.1 hP.1
  have hcomp1 : (1-p-(lam+delta))*0.1788 ≤ 0.187675*0.1788 := by
    linarith [hp.1,hLnew.1]
  have hcomp2 := mul_le_mul hLnew.1
    (show (0.26 : ℝ) ≤ 0.62-p by linarith [hp.2]) (by norm_num : (0 : ℝ) ≤ 0.26)
    (by linarith [hLnew.1] : 0 ≤ lam+delta)
  have hcompCoef : (1-p-(lam+delta))*0.1788-(lam+delta)*(0.62-p) ≤ 0 := by
    nlinarith only [hcomp1,hcomp2]
  have hcompGain := mul_nonpos_of_nonneg_of_nonpos hs.1 hcompCoef
  dsimp only
  refine ⟨⟨by linarith [hR.1],by linarith [hR.2]⟩,by linarith [hP.1],?_,?_,?_⟩
  · unfold Certificates.Control.det
    nlinarith only [hD,hdeltaD,hdetgain]
  · nlinarith only [hB,hdeltaB,hBg,hBloss,hsmax]
  · nlinarith only [hcomp,hcompBase,hcompGain]

end OptimalG.Variational.ParameterTransfer
