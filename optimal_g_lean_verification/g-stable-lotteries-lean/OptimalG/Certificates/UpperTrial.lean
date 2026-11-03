import OptimalG.Certificates.UpperProfileData
import OptimalG.Certificates.CapCubic
import OptimalG.Certificates.CubicEvaluation
import OptimalG.VariationalDefs

/-! The corrected upper-endpoint trial belongs to the actual low-rank class.
This proves admissibility, not the high-rank ODE terminal inequalities. -/

namespace OptimalG.Certificates.UpperTrial
open MeasureTheory Set
open UpperProfileData
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def score : ℝ → ℝ := capCubicScore lam slack leftContact pieces
noncomputable def primitive : ℝ → ℝ := capCubicPrimitive lam slack leftContact pieces

theorem contact_range : (0.295:ℝ)<leftContact ∧ (leftContact:ℝ)<0.296 := by
  constructor
  · have h : ((0.295:ℚ):ℝ)<(leftContact:ℝ) := Rat.cast_lt.mpr contacts.1
    norm_num at h ⊢
    exact h
  · have h : (leftContact:ℝ)<((0.296:ℚ):ℝ) := Rat.cast_lt.mpr contacts.2.1
    norm_num at h ⊢
    exact h

private theorem contact_lt_one : (leftContact:ℝ)<1 := by
  have h : (leftContact:ℝ)<0.296 := contact_range.2
  linarith

theorem initial_joins :
    cap lam slack leftContact=cubicPrimitive lam slack pieces leftContact ∧
    capSlope lam slack leftContact=cubicScore lam pieces leftContact := by
  have hp : piece0.lo≤piece0.hi := by decide +kernel
  have hl : pieces=piece0::pieces.tail := rfl
  have hs := cubicScore_at_first lam piece0 pieces.tail hp
  have hf := cubicPrimitive_at_first lam slack piece0 pieces.tail hp
  rw [← hl,endpoint_data.1] at hs hf
  have hsc : (piece0.a0:ℝ)=capSlope lam slack leftContact := by
    have h := congrArg (fun q:ℚ => (q:ℝ)) endpoint_data.2.2.1
    simpa [capSlope] using h
  have hfc : (piece0.f0:ℝ)=cap lam slack leftContact := by
    have h := congrArg (fun q:ℚ => (q:ℝ)) endpoint_data.2.2.2.1
    simpa [cap] using h
  exact ⟨(hf.trans hfc).symm,(hs.trans hsc).symm⟩

theorem continuous_score : Continuous score :=
  capCubic_continuousScore contact_lt_one assembly_checked initial_joins.2

theorem primitive_hasDerivAt (r : ℝ) : HasDerivAt primitive (score r) r :=
  capCubic_hasDerivAt contact_lt_one assembly_checked initial_joins.1 initial_joins.2 r

theorem primitive_left : primitive 0.28=cap lam slack 0.28 := by
  have hc : (0.28:ℝ)≤leftContact := by
    have hh : (0.295:ℝ)<leftContact := contact_range.1
    linarith
  exact if_pos hc

theorem primitive_integral (r : ℝ) :
    cap lam slack 0.28+(∫ t in (0.28:ℝ)..r, score t)=primitive r := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => primitive_hasDerivAt t) (continuous_score.intervalIntegrable 0.28 r),primitive_left]
  ring

theorem primitive_right : primitive 0.385=quadratic lam 0.385-slack := by
  have hc : ¬(0.385:ℝ)≤leftContact := by
    have hh : (leftContact:ℝ)<0.296 := contact_range.2
    linarith
  have hh : ∀ p∈pieces, (p.hi:ℝ)<(0.385:ℝ) := by
    intro p hp
    have hd : decide (p.hi<(0.385:ℚ))=true := (List.all_eq_true.mp all_before_end) p hp
    have he : p.hi<(0.385:ℚ) := of_decide_eq_true hd
    have he' : (p.hi:ℝ)<((0.385:ℚ):ℝ) := Rat.cast_lt.mpr he
    norm_num at he' ⊢
    exact he'
  unfold primitive capCubicPrimitive
  rw [if_neg hc]
  exact (cubic_tail_values lam slack 0.385 pieces hh).2

/-- Every real rank of the full low-rank interval satisfies the score and cap
constraints, with the exact cap prefix and all 242 cubic pieces included. -/
theorem bounds {r : ℝ} (hr : r∈Icc (0.28:ℝ) 0.385) :
    0≤score r ∧ score r≤(lam:ℝ)-r ∧ primitive r≤cap lam slack r := by
  by_cases hc : r≤leftContact
  · have hh : (leftContact:ℝ)<0.296 := contact_range.2
    have hpre := capSlope_bounds (L:=(lam:ℝ)) (S:=(slack:ℝ))
      (by norm_num [lam]) (by norm_num [slack]) ⟨hr.1,by linarith⟩
    simpa only [score,primitive,capCubicScore,capCubicPrimitive,if_pos hc] using
      ⟨hpre.1,hpre.2,le_refl (cap (lam:ℝ) (slack:ℝ) r)⟩
  · have hfree := assembled_bounds ⟨le_of_lt (lt_of_not_ge hc),hr.2⟩
    simpa only [score,primitive,capCubicScore,capCubicPrimitive,if_neg hc] using hfree

end OptimalG.Certificates.UpperTrial

namespace OptimalG.Variational
open MeasureTheory Set

noncomputable def upperTrialData : LowRankData :=
  ⟨Certificates.UpperProfileData.slack,Certificates.UpperTrial.score⟩

theorem lowPrimitive_upperTrial (r : ℝ) :
    lowPrimitive Certificates.UpperProfileData.lam upperTrialData r=
      Certificates.UpperTrial.primitive r := by
  have h := Certificates.UpperTrial.primitive_integral r
  change cap Certificates.UpperProfileData.lam Certificates.UpperProfileData.slack ell+
    (∫ t in ell..r, Certificates.UpperTrial.score t)=_
  norm_num [ell,cap,Certificates.cap] at h ⊢
  exact h

/-- A kernel-checked admissible datum at the proposed upper endpoint. The
separate high-rank continuation and terminal checks are not premises here. -/
theorem upperTrial_admissible :
    Admissible Certificates.UpperProfileData.lam upperTrialData := by
  have hb : ∀ᵐ r ∂volume.restrict (Icc ell tEnd),
      0≤Certificates.UpperTrial.score r ∧
      Certificates.UpperTrial.score r≤(Certificates.UpperProfileData.lam:ℝ)-r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hr' : r∈Icc (0.28:ℝ) 0.385 := by norm_num [ell,tEnd] at hr ⊢; exact hr
    exact (Certificates.UpperTrial.bounds hr').imp_right And.left
  have hnorm : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), ‖Certificates.UpperTrial.score r‖≤1 := by
    filter_upwards [hb,ae_restrict_mem measurableSet_Icc] with r hs hr
    rw [Real.norm_eq_abs,abs_of_nonneg hs.1]
    have hr0 := hr.1
    norm_num [ell] at hr0
    have hh := hs.2
    norm_num [Certificates.UpperProfileData.lam] at hh
    linarith
  refine ⟨?_,?_,?_,hb,?_,?_⟩
  · norm_num [lambdaLo,lambdaHi,Certificates.UpperProfileData.lam]
  · norm_num [upperTrialData,slackUpper,lambdaHi,Certificates.UpperProfileData.lam,
      Certificates.UpperProfileData.slack]
  · exact memLp_top_of_bound Certificates.UpperTrial.continuous_score.aestronglyMeasurable 1 hnorm
  · rw [lowPrimitive_upperTrial]
    convert Certificates.UpperTrial.primitive_right using 1 <;>
      norm_num [tEnd,quadratic,Certificates.quadratic,upperTrialData]
  · intro r hr
    rw [lowPrimitive_upperTrial]
    have hr' : r∈Icc (0.28:ℝ) 0.385 := by norm_num [ell,tEnd] at hr ⊢; exact hr
    exact (Certificates.UpperTrial.bounds hr').2.2

end OptimalG.Variational
