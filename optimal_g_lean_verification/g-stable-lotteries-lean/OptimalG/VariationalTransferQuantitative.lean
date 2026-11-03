import OptimalG.VariationalControlPerturbation
import OptimalG.ParameterTransfer
import OptimalG.VariationalODELimit

/-! Uniform reverse estimates for the actual B.2 parameter transfer. These
bounds prevent a localization estimate for the transferred trajectory from
being incorrectly used in the opposite direction without an error term. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

 theorem transferred_control_change {lam delta z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) {v : Control} (hv : v ∈ controlDomain)
    (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S)
    (hA : 0 ≤ d.phi v.2.1 ∧ d.phi v.2.1 ≤ lam-v.2.1)
    (hB : 0 ≤ d.phi v.2.2 ∧ d.phi v.2.2 ≤ lam-v.2.2) :
    |signedControlH (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta)
        (rawAlpha (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
        (rawBeta (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
        (·.1) z u v-controlH lam d z u v| ≤ 50*delta := by
  obtain ⟨hp,hx,hy⟩ := ParameterTransfer.control_ranges hv
  have hL := hd.compact_lambdaRange
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by
    convert! hz using 1 <;> norm_num [zStart,zEnd]
  have hdeltaMax : delta ≤ (0.000005 : ℝ) := by linarith [hL.1,hLnew.2]
  have hR0 := hd.control_R_lower hv.1
  have hR1 := ParameterTransfer.Admissible_control_R_small hd hv.1
  have hP0 := hd.control_P_bounds hv.1
  have hK0 := hd.control_K_bounds hv.1 hz huLow huHigh
  let R := primitive lam d v.1
  let P := quadratic lam (1-v.1)-d.S
  let K := quadratic lam (z-v.1)-d.S-u
  have hRb : |R| ≤ (0.14 : ℝ) := abs_le.mpr ⟨by dsimp [R];linarith,by dsimp [R];linarith⟩
  have hPb : |P| ≤ (0.16 : ℝ) := abs_le.mpr ⟨by dsimp [P];linarith [hP0.1],by dsimp [P];linarith [hP0.2]⟩
  have hKb : |K| ≤ (0.12 : ℝ) := abs_le.mpr ⟨by dsimp [K];linarith [hK0.1],by dsimp [K];linarith [hK0.2]⟩
  have hRn : |R+0.1788*delta| ≤ (0.14 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [R] <;> linarith
  have hPg0 := mul_nonneg hdelta (show 0 ≤ 0.7988-v.1 by linarith [hp.2])
  have hPg1 := mul_le_mul_of_nonneg_left
    (show 0.7988-v.1 ≤ (0.5488 : ℝ) by linarith [hp.1]) hdelta
  have hPn : |P+delta*(0.7988-v.1)| ≤ (0.16 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [P] <;> linarith [hP0.1,hP0.2]
  have hU : |z-lam| ≤ (0.334 : ℝ) := abs_le.mpr ⟨by linarith [hz'.1,hL.2],by linarith [hz'.2,hL.1]⟩
  have hh : |2*lam-v.2.1| ≤ (0.85 : ℝ) := abs_le.mpr ⟨by linarith [hL.1,hx.2],by linarith [hL.2,hx.1]⟩
  have hhn : |2*(lam+delta)-v.2.1| ≤ (0.85 : ℝ) := abs_le.mpr ⟨by linarith [hLnew.1,hx.2],by linarith [hLnew.2,hx.1]⟩
  have hk : |v.1+v.2.2-lam| ≤ (0.18 : ℝ) := abs_le.mpr ⟨by linarith [hp.1,hy.1,hL.2],by linarith [hp.2,hy.2,hL.1]⟩
  have hkn : |v.1+v.2.2-(lam+delta)| ≤ (0.18 : ℝ) := abs_le.mpr ⟨by linarith [hp.1,hy.1,hLnew.2],by linarith [hp.2,hy.2,hLnew.1]⟩
  have hAa : |d.phi v.2.1| ≤ (0.278 : ℝ) := by rw [abs_of_nonneg hA.1];linarith [hA.2,hL.2,hx.1]
  have hBa : |d.phi v.2.2| ≤ (0.278 : ℝ) := by rw [abs_of_nonneg hB.1];linarith [hB.2,hL.2,hy.1]
  have hdU : |(z-(lam+delta))-(z-lam)| ≤ delta := by
    have he : (z-(lam+delta))-(z-lam)= -delta := by ring
    rw [he,abs_neg,abs_of_nonneg hdelta]
  have hdK : |(K+delta*(z-v.1-0.2012))-K| ≤ delta := by
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hdelta,
      abs_of_nonneg (by linarith [hz'.1,hp.2] : 0 ≤ z-v.1-0.2012)]
    nlinarith only [mul_le_mul_of_nonneg_left (show z-v.1-0.2012 ≤ (1:ℝ) by linarith [hz'.2,hp.1]) hdelta]
  have hdh : |(2*(lam+delta)-v.2.1)-(2*lam-v.2.1)| ≤ 2*delta := by
    have he : (2*(lam+delta)-v.2.1)-(2*lam-v.2.1)=2*delta := by ring
    rw [he,abs_of_nonneg (by positivity)]
  have hdk : |(v.1+v.2.2-(lam+delta))-(v.1+v.2.2-lam)| ≤ delta := by
    have he : (v.1+v.2.2-(lam+delta))-(v.1+v.2.2-lam)= -delta := by ring
    rw [he,abs_neg,abs_of_nonneg hdelta]
  have hdR : |(R+0.1788*delta)-R| ≤ delta := by
    rw [add_sub_cancel_left,abs_of_nonneg (by positivity)]
    linarith
  have hdP : |(P+delta*(0.7988-v.1))-P| ≤ delta := by
    rw [add_sub_cancel_left,abs_of_nonneg hPg0]
    linarith
  obtain ⟨hRv,hPv,hKv⟩ := ParameterTransfer.shifted_control_values lam delta d hv hz
  have hD : (0.0519 : ℝ) ≤ (2*lam-v.2.1)*R-(v.1+v.2.2-lam)*P := hd.determinant_sharp hv |>.le
  have hDn : (0.0519 : ℝ) ≤ (2*(lam+delta)-v.2.1)*(R+0.1788*delta)-
      (v.1+v.2.2-(lam+delta))*(P+delta*(0.7988-v.1)) := by
    have hi := ParameterTransfer.shifted_determinant hd hLnew hdelta hv
    rw [rawDet,hRv,hPv] at hi
    convert! hi using 1 <;> dsimp [R,P] <;> ring
  have hi := finite_control_perturbation hdelta hU hKb hh hhn hk hkn hRb hRn hPb hPn hAa hBa
    hdU hdK hdh hdk hdR hdP hD hDn
  rw [rawControl_eq_value,hRv,hPv,hKv,controlH_eq_certified_value]
  convert! hi using 1 <;> dsimp [R,P,K] <;> ring

 theorem transferred_alpha_abs_le {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) :
    ∀ᵐ v ∂controlMeasure,
      |rawAlpha (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi v| ≤ (6 : ℝ) := by
  filter_upwards [ae_restrict_mem controlDomain_measurable,
    ae_control_lowRanks _ hd.2.2.2.1] with v hv hphi
  obtain ⟨hp,hx,hy⟩ := ParameterTransfer.control_ranges hv
  have hL := hd.compact_lambdaRange
  have hh : |2*(lam+delta)-v.2.1| ≤ (0.85 : ℝ) := abs_le.mpr ⟨by linarith [hLnew.1,hx.2],by linarith [hLnew.2,hx.1]⟩
  have hk : |v.1+v.2.2-(lam+delta)| ≤ (0.18 : ℝ) := abs_le.mpr ⟨by linarith [hp.1,hy.1,hLnew.2],by linarith [hp.2,hy.2,hLnew.1]⟩
  have hA : |d.phi v.2.1| ≤ (0.278 : ℝ) := by
    rw [abs_of_nonneg hphi.1.1]
    linarith [hphi.1.2,hL.2,hx.1]
  have hB : |d.phi v.2.2| ≤ (0.278 : ℝ) := by
    rw [abs_of_nonneg hphi.2.1]
    linarith [hphi.2.2,hL.2,hy.1]
  have hN := score_linear_bound hk hh hA hB (by norm_num) (by norm_num)
  have hD := ParameterTransfer.shifted_determinant hd hLnew hdelta hv
  have hDp : 0 < rawDet (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) v := by linarith
  rw [rawAlpha,abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  linarith

 theorem transferred_field_state_lipschitz {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (z : ℝ) :
    LipschitzWith 6 (rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi z) := by
  have hs := hd.control_basic_bounded
  have hcoeff := raw_coefficients_bounded (ParameterTransfer.shiftedPrimitive_lipschitz hd delta)
    (by norm_num : (0 : ℝ) < 0.0519)
    (fun v hv => ParameterTransfer.shifted_determinant hd hLnew hdelta hv) hs.2.2.1 hs.2.2.2.1
  exact signedVectorField_state_lipschitz (ParameterTransfer.shiftedPrimitive_lipschitz hd delta)
    (transferred_alpha_abs_le hd hLnew hdelta) hcoeff.2 control_coordinates_bounded.1 z

 theorem transferred_field_change {lam delta z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S) :
    |rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi z u-
      vectorField lam d z u| ≤ 50*delta := by
  have hs := hd.control_basic_bounded
  have hcoeff := raw_coefficients_bounded (ParameterTransfer.shiftedPrimitive_lipschitz hd delta)
    (by norm_num : (0 : ℝ) < 0.0519)
    (fun v hv => ParameterTransfer.shifted_determinant hd hLnew hdelta hv) hs.2.2.1 hs.2.2.2.1
  have hb := signedControlH_bounded (lam := lam+delta) (ParameterTransfer.shiftedPrimitive_lipschitz hd delta)
    hcoeff.1 hcoeff.2 control_coordinates_bounded.1 z u
  have hc := hd.controlH_bounded z u
  have hdiff : ∀ᵐ v ∂controlMeasure,
      |signedControlH (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta)
        (rawAlpha (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
        (rawBeta (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
        (·.1) z u v-controlH lam d z u v| ≤ 50*delta := by
    filter_upwards [ae_restrict_mem controlDomain_measurable,
      ae_control_lowRanks _ hd.2.2.2.1] with v hv hphi
    exact transferred_control_change hd hLnew hdelta hv hz huLow huHigh hphi.1 hphi.2
  have h1 := essInf_le_add_of_ae_le (50*delta) hb hc (by
    filter_upwards [hdiff] with v hv
    linarith [(abs_le.mp hv).2])
  have h2 := essInf_le_add_of_ae_le (50*delta) hc hb (by
    filter_upwards [hdiff] with v hv
    linarith [(abs_le.mp hv).1])
  have hess : |essInf (signedControlH (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta)
      (rawAlpha (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
      (rawBeta (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
      (·.1) z u) controlMeasure-essInf (controlH lam d z u) controlMeasure| ≤ 50*delta :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  unfold rawVectorField signedVectorField vectorField
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  refine max_le ?_ hess
  have he : (lam+delta-z)-(lam-z)=delta := by ring
  rw [he,abs_of_nonneg hdelta]
  linarith

 theorem transferred_trajectory_error {lam delta b : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (hY : IsContinuation lam d Y) (hpass : PassesTerminalTests lam d Y)
    (T : ParameterTransfer.UpwardTransfer lam delta d Y) (hb : b ∈ Icc zStart zEnd) :
    ∀ z ∈ Icc zStart b, |T.trajectory z-Y z| ≤
      Real.exp (6*(b-zStart))*(0.5738+50*(b-zStart))*delta := by
  have hsub : Icc zStart b ⊆ Icc zStart zEnd := Icc_subset_Icc le_rfl hb.2
  have hYCfull : ContinuousOn Y (Icc zStart zEnd) := fun z hz => (hY.2 z hz).continuousWithinAt
  have hTCfull : ContinuousOn T.trajectory (Icc zStart zEnd) := fun z hz => (T.derivative z hz).continuousWithinAt
  have hYC := hYCfull.mono hsub
  have hTC := hTCfull.mono hsub
  have hinit : |T.trajectory zStart-Y zStart|=0.5738*delta := by
    rw [T.initial,hY.1]
    have he : quadratic (lam+delta) zStart-ParameterTransfer.scalar d.S delta-
        (quadratic lam zStart-d.S)=0.5738*delta := by
      dsimp [quadratic,ParameterTransfer.scalar,zStart]
      ring
    rw [he,abs_of_nonneg (by positivity)]
  have hi := scalar_ode_l1_gap
    (rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi)
    6 Y T.trajectory (fun z => vectorField lam d z (Y z)) (fun _ => 50*delta) zStart b hb.1
    (fun z _ => transferred_field_state_lipschitz hd hLnew hdelta z) hYC hTC
    (fun z hz => hY.right_derivative ⟨hz.1,hz.2.trans_le hb.2⟩)
    (fun z hz => (T.derivative z (hsub ⟨hz.1,hz.2.le⟩)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (show z ∈ Ico zStart zEnd from ⟨hz.1,hz.2.trans_le hb.2⟩)))
    continuousOn_const (fun _ _ => by positivity) (fun z hz =>
      transferred_field_change hd hLnew hdelta (hsub ⟨hz.1,hz.2.le⟩)
        (by linarith [hd.continuation_above_root_budget hY hpass (hsub ⟨hz.1,hz.2.le⟩)])
        (hd.continuation_le_quadratic hY _ (hsub ⟨hz.1,hz.2.le⟩)))
  intro z hz
  have hh := hi z hz
  rw [hinit,intervalIntegral.integral_const] at hh
  convert! hh using 1 <;> simp only [NNReal.coe_ofNat,smul_eq_mul] <;> ring

 theorem transferred_initial_segment_error {lam delta z : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (hY : IsContinuation lam d Y) (hpass : PassesTerminalTests lam d Y)
    (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : z ∈ Icc zStart 0.784) : |T.trajectory z-Y z| ≤ 1.1*delta := by
  have htime : z ∈ Icc zStart zEnd := ⟨hz.1,hz.2.trans (by norm_num [zEnd])⟩
  have hh := transferred_trajectory_error hd hLnew hdelta hY hpass T htime z ⟨hz.1,le_rfl⟩
  have hstep : 0 ≤ z-zStart ∧ z-zStart ≤ (0.009 : ℝ) := by
    constructor <;> norm_num [zStart] at hz ⊢ <;> linarith [hz.1,hz.2]
  have he := Real.add_one_le_exp (-(6*(z-zStart)))
  have hmul := mul_le_mul_of_nonneg_right he (Real.exp_pos (6*(z-zStart))).le
  rw [Real.exp_neg,inv_mul_cancel₀ (ne_of_gt (Real.exp_pos (6*(z-zStart))))] at hmul
  have hproduct := mul_le_mul_of_nonneg_right
    (show 6*(z-zStart) ≤ (0.054 : ℝ) by linarith [hstep.2])
    (Real.exp_pos (6*(z-zStart))).le
  have hexp : Real.exp (6*(z-zStart)) ≤ (1.06 : ℝ) := by nlinarith only [hmul,hproduct]
  have hcoef := mul_le_mul hexp
    (show 0.5738+50*(z-zStart) ≤ (1.0238 : ℝ) by linarith [hstep.2])
    (show 0 ≤ 0.5738+50*(z-zStart) by linarith [hstep.1]) (by norm_num : (0 : ℝ) ≤ 1.06)
  have hfinal := mul_le_mul_of_nonneg_right hcoef hdelta
  nlinarith only [hh,hfinal,hdelta]

 theorem original_high_deficit_le_transferred {lam delta z : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (hY : IsContinuation lam d Y) (hpass : PassesTerminalTests lam d Y)
    (T : ParameterTransfer.UpwardTransfer lam delta d Y) (hz : z ∈ Icc zStart 0.784) :
    quadratic lam z-d.S-Y z ≤
      quadratic (lam+delta) z-ParameterTransfer.scalar d.S delta-T.trajectory z+0.5262*delta := by
  have he := transferred_initial_segment_error hd hLnew hdelta hY hpass T hz
  have hz' : (0.775 : ℝ) ≤ z := by convert! hz.1 using 1 <;> norm_num [zStart]
  have hm := mul_le_mul_of_nonneg_left hz' hdelta
  have hu := (le_abs_self (T.trajectory z-Y z)).trans he
  dsimp [quadratic,ParameterTransfer.scalar]
  nlinarith only [hu,hm]

end OptimalG.Variational
