import OptimalG.Certificates.StaticBinaryCentralExpressions
import OptimalG.Certificates.StaticHighParameters
import OptimalG.BinaryLateAssembly

/-! Exact scalar and polynomial-tail inputs for the static late binary test. -/
namespace OptimalG.Certificates.StaticBinaryLateScalars
open Set StaticBinaryCentralExpressions

noncomputable def B : ℝ := (StaticHigh.tailSlope:ℝ)/2-1
noncomputable def C : ℝ := (StaticHigh.tailCurvature:ℝ)/3

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem bound_pos : 0<B := by norm_num [B,StaticHigh.tailSlope]
theorem curvature_bound : B≤C := by norm_num [B,C,StaticHigh.tailSlope,StaticHigh.tailCurvature]
theorem endpoint_bound : B*(L-337/1000)≤1/2 := by
  norm_num [B,L,StaticHigh.tailSlope,StaticLow.lam]
theorem coefficient_bound : (1/2:ℝ)≤C*(L-337/1000) := by
  norm_num [C,L,StaticHigh.tailCurvature,StaticLow.lam]

theorem width_nonneg {d : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80)) :
    0≤(B-C*d)/(1-d) := by
  have hB : (214/100:ℝ)≤B := by norm_num [B,StaticHigh.tailSlope]
  have hC : C≤385/100 := by norm_num [C,StaticHigh.tailCurvature]
  have hh := mul_le_mul_of_nonneg_right hC (by linarith only [hd.1] : 0≤d)
  exact div_nonneg (by nlinarith only [hB,hh,hd.2]) (by linarith only [hd.2])

theorem width_high {d : ℝ} (hd : d∈Icc (1/50:ℝ) (7/80)) :
    ((B-C*d)/(1-d))*(L-337/1000)≤1/2 := by
  have hd0 : 0≤d := by linarith only [hd.1]
  have hden : 0<1-d := by linarith only [hd.2]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have hh := mul_le_mul_of_nonneg_right coefficient_bound hd0
  nlinarith only [endpoint_bound,hh]

theorem small_rank : B*L≤50*binaryScoreLower L S initial
    StaticBinaryCentralExpressions.slope (527/2000) c (7189/20000) (309/1000)
      (27/100)+1/2 := by
  norm_num [binaryScoreLower,L,S,c,StaticLow.lam,StaticLow.slack,
    StaticLow.leftContact,UpperProfileData.leftContact,B,StaticHigh.tailSlope,
    Variational.capSlack,Variational.capScore]

theorem tail_coefficients :
    tailBackwardSlope StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/2-1=B ∧
    tailBackwardCurvature StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/3=C := by
  norm_num [tailBackwardSlope,tailBackwardCurvature,tailOne,tailTwo,B,C,
    StaticHigh.contact,StaticHigh.contactValue,StaticHigh.contactScore,
    StaticHigh.tailSlope,StaticHigh.tailCurvature]

theorem tail_majorant :
    tailBackwardSlope StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/2-1≤B ∧
    tailBackwardSlope StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/2-1≤
      tailBackwardCurvature StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/3 ∧
    tailBackwardSlope StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/2-1-
      (tailBackwardCurvature StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore/3)*(7/80)≤
      B-C*(7/80) := by
  rw [tail_coefficients.1,tail_coefficients.2]
  exact ⟨le_rfl,curvature_bound,le_rfl⟩

end OptimalG.Certificates.StaticBinaryLateScalars
