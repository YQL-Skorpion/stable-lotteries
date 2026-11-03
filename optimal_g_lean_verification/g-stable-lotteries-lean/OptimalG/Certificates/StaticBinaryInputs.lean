import OptimalG.Certificates.StaticCurve
import OptimalG.Certificates.StaticContactGeometry
import OptimalG.Certificates.StaticTerminal
import OptimalG.Certificates.StaticBinaryLateScalars
import OptimalG.CompletedCurveFacts

/-! Actual geometric inputs for the rational upper-bound binary certificate. -/
namespace OptimalG.Certificates.StaticBinaryInputs
open Set

noncomputable def Y : ℝ → ℝ :=
  joinAt StaticHigh.contact StaticCurve.primitive StaticTerminal.parabola

theorem actual {p : ℝ} (hp : p≤(StaticHigh.contact:ℝ)) :
    StaticCurve.primitive p=Y p := (joinAt_left _ _ hp).symm

theorem after_contact {p : ℝ} (hp : (StaticHigh.contact:ℝ)≤p) :
    Y p=StaticTerminal.parabola p := by
  apply joinAt_right _ _ hp
  rw [StaticCurve.contact_values.2]
  simp only [StaticTerminal.parabola,sub_self,mul_zero,add_zero,zero_pow (by decide : 2≠0),sub_zero]

theorem continuous : ContinuousOn Y (Icc (31/40:ℝ) StaticHigh.contact) := by
  apply (StaticCurve.verifierCurve.primitive_continuous.mono
    (Icc_subset_Icc (by norm_num) (by norm_num [StaticHigh.contact]))).congr
  intro p hp
  exact (actual hp.2).symm

theorem derivative {p : ℝ} (hp : p∈Ioo (31/40:ℝ) StaticHigh.contact) :
    HasDerivAt Y (StaticCurve.score p) p := by
  have hd := StaticCurve.verifierCurve.primitive_hasDerivAt
    (show p∈Ioo (0:ℝ) 1 from ⟨by linarith only [hp.1],hp.2.trans
      (by norm_num [StaticHigh.contact])⟩)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hp.2] with r hr
  exact (actual hr.le).symm

theorem initial : StaticCurve.score 0=StaticBinaryCentralExpressions.initial := by
  rw [StaticCurve.initial_value]
  norm_num [StaticBinaryCentralExpressions.initial,SmallMassExpressions.initial,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,
    headInitial,cap,capSlope,Variational.cap,Variational.capScore]

theorem slope : StaticLow.affineHeadSlope=StaticBinaryCentralExpressions.slope := by
  norm_num [StaticLow.affineHeadSlope,StaticBinaryCentralExpressions.slope,
    SmallMassExpressions.slope,StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,
    headSlope,cap,capSlope,Variational.cap,Variational.capScore]

theorem reference_values :
    binarySlackArea StaticCurve.score StaticLow.lam StaticLow.slack (348541/1000000)=0 ∧
    scoreDefect StaticCurve.score StaticLow.lam (348541/1000000)=0 := by
  have hr : (348541/1000000:ℝ)∈Icc (StaticLow.rightContact:ℝ) StaticHigh.departure := by
    norm_num [StaticLow.rightContact,UpperProfileData.rightContact,StaticHigh.departure]
  have hh := StaticCurve.line_values hr
  change curvePrimitive StaticCurve.score _-_+_=0 ∧ (StaticLow.lam:ℝ)-_-_=0
  rw [show curvePrimitive StaticCurve.score (348541/1000000)=
    Variational.quadratic StaticLow.lam (348541/1000000)-StaticLow.slack from hh.2,hh.1]
  constructor <;> ring

theorem slack_pos : 0<Variational.capSlack StaticLow.lam StaticLow.slack StaticLow.leftContact := by
  norm_num [Variational.capSlack,Variational.capScore,StaticLow.lam,StaticLow.slack,
    StaticLow.leftContact,UpperProfileData.leftContact]

end OptimalG.Certificates.StaticBinaryInputs
