import OptimalG.Certificates.HighMassData.IntermediateBeta
import OptimalG.Certificates.HighMassData.IntermediateMargin
import OptimalG.Certificates.HighMassData.IntermediateCorrection
import OptimalG.Certificates.HighMassData.IntermediateEtaZero
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.HighMassGeometry

namespace OptimalG.Certificates.HighMassBasic
open Set SmallMassExpressions

theorem IntermediateBeta_identity (lam S p : ℝ) :
    HighMassData.IntermediateBeta.numerator lam S p=(2483/500)*(Variational.quadratic lam p-S)-p := by
  norm_num [HighMassData.IntermediateBeta.numerator,SmallMassExpressions.initial,
    headInitial,Variational.capScore,Variational.cap,Variational.quadratic]
  <;> ring

theorem IntermediateMargin_identity (lam S p : ℝ) :
    HighMassData.IntermediateMargin.numerator lam S p=p*(SmallMassExpressions.initial lam S-lam+1-p)-(Variational.quadratic lam p-S) := by
  norm_num [HighMassData.IntermediateMargin.numerator,SmallMassExpressions.initial,
    headInitial,Variational.capScore,Variational.cap,Variational.quadratic]
  <;> ring

theorem IntermediateCorrection_identity (lam S p : ℝ) :
    HighMassData.IntermediateCorrection.numerator lam S p=(1/10-lam)*(Variational.quadratic lam p-S)+p*(Variational.quadratic lam (1-p)-S) := by
  norm_num [HighMassData.IntermediateCorrection.numerator,SmallMassExpressions.initial,
    headInitial,Variational.capScore,Variational.cap,Variational.quadratic]
  <;> ring

theorem IntermediateEtaZero_identity (lam S p : ℝ) :
    HighMassData.IntermediateEtaZero.numerator lam S p=Variational.capScore lam S (527/2000)*(lam-SmallMassExpressions.initial lam S)-(1/10)*(SmallMassExpressions.initial lam S-Variational.capScore lam S (527/2000)) := by
  norm_num [HighMassData.IntermediateEtaZero.numerator,SmallMassExpressions.initial,
    headInitial,Variational.capScore,Variational.cap,Variational.quadratic]
  <;> ring

/-- Three scalar C5 requirements, interpreted for the actual curve. -/
theorem intermediate_bounds {phi : ℝ→ℝ} {lam S p : ℝ}
    (h : VerifierCurve phi lam)
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Ioc lam (13/20:ℝ))
    (hJ : curvePrimitive phi p=Variational.quadratic lam p-S)
    (hP : Variational.quadratic lam (1-p)-S≤curvePrimitive phi (1-p))
    (hzero : phi 0=initial lam S)
    (hhead : phi (527/2000)=Variational.capScore lam S (527/2000)) :
    p/curvePrimitive phi p≤2483/500 ∧
    curvePrimitive phi p≤p*(phi 0-lam+1-p) ∧
    intermediateCorrection phi lam p≤1/10 ∧
    intermediateEta phi lam (527/2000) p*phi 0≤lam+intermediateCorrection phi lam p := by
  have hp' : p∈Icc (22493/40000:ℝ) (13/20) := ⟨hL.1.trans hp.1.le,hp.2⟩
  have hIntermediateBeta := HighMassData.IntermediateBeta.numerator_pos hL hS hp'
  rw [IntermediateBeta_identity] at hIntermediateBeta
  have hIntermediateMargin := HighMassData.IntermediateMargin.numerator_pos hL hS hp'
  rw [IntermediateMargin_identity] at hIntermediateMargin
  have hIntermediateCorrection := HighMassData.IntermediateCorrection.numerator_pos hL hS hp'
  rw [IntermediateCorrection_identity] at hIntermediateCorrection
  have hIntermediateEtaZero := HighMassData.IntermediateEtaZero.numerator_pos hL hS hp'
  rw [IntermediateEtaZero_identity] at hIntermediateEtaZero
  have hp0 : 0<p := h.lam_pos.trans hp.1
  have hp1 : p<1 := by linarith only [hp.2]
  have hJpos := h.primitive_pos ⟨hp0,hp1⟩
  have hR : 0<Variational.quadratic lam p-S := by rwa [hJ] at hJpos
  have hb := (div_pos hp0 hR).le
  have hq : lam-1/10≤(p/(Variational.quadratic lam p-S))*(Variational.quadratic lam (1-p)-S) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hR).mpr
    nlinarith only [hIntermediateCorrection]
  have hscaled := mul_le_mul_of_nonneg_left hP hb
  have hci : intermediateCorrection phi lam p≤1/10 := by
    unfold intermediateCorrection
    rw [hJ]
    linarith only [hq,hscaled]
  refine ⟨?_,?_,hci,?_⟩
  · rw [hJ]
    apply (div_le_iff₀ hR).mpr
    linarith only [hIntermediateBeta]
  · rw [hJ,hzero]
    linarith only [hIntermediateMargin]
  · have hhpos : 0<Variational.capScore lam S (527/2000) := by
      rw [←hhead]
      exact h.positive ⟨by norm_num,by linarith only [hL.1]⟩
    have hmono := h.decreasing.antitoneOn
      (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
      (show (527/2000:ℝ)∈Icc 0 1 by constructor <;> norm_num)
      (by norm_num : (0:ℝ)≤527/2000)
    rw [hzero,hhead] at hmono
    have hm := mul_le_mul_of_nonneg_right hci (sub_nonneg.mpr hmono)
    have hquot : intermediateCorrection phi lam p*initial lam S/
        Variational.capScore lam S (527/2000)≤
        lam+intermediateCorrection phi lam p-initial lam S := by
      apply (div_le_iff₀ hhpos).mpr
      nlinarith only [hm,hIntermediateEtaZero]
    rw [intermediateEta,hhead,hzero,add_mul,one_mul,div_mul_eq_mul_div]
    linarith only [hquot]

end OptimalG.Certificates.HighMassBasic
