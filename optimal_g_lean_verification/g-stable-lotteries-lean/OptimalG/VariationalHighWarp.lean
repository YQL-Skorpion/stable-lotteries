import OptimalG.VariationalTransferredLogControl

/-! The scalar-dependent affine high-rank warp preserves the initial time.
The actual continuation ceiling supplies positivity of the logarithmic deficit
throughout the warped interval from one initial quadratic gap. -/
namespace OptimalG.Variational
open Set Real
open scoped NNReal

noncomputable def highWarp (a b ds s : ℝ) : ℝ := s-(s-a)/(b-a)*ds
noncomputable def highWarpSlope (a b ds : ℝ) : ℝ := 1-ds/(b-a)

theorem highWarp_affine (a b ds s : ℝ) :
    highWarp a b ds s=highWarpSlope a b ds*(s-a)+a := by
  unfold highWarp highWarpSlope
  ring

@[simp] theorem highWarp_initial (a b ds : ℝ) : highWarp a b ds a=a := by
  simp [highWarp]

theorem highWarp_terminal {a b : ℝ} (hab : a<b) (ds : ℝ) :
    highWarp a b ds b=b-ds := by
  simp only [highWarp,div_self (sub_ne_zero.mpr hab.ne'),one_mul]

theorem highWarpSlope_pos {a b ds : ℝ} (hab : a<b) (hds : ds<b-a) :
    0<highWarpSlope a b ds := by
  unfold highWarpSlope
  exact sub_pos.mpr ((div_lt_one (sub_pos.mpr hab)).mpr hds)

theorem highWarp_hasDerivAt (a b ds s : ℝ) :
    HasDerivAt (highWarp a b ds) (highWarpSlope a b ds) s := by
  have he : highWarp a b ds=(fun s=>highWarpSlope a b ds*(s-a)+a) :=
    funext (highWarp_affine a b ds)
  rw [he]
  convert! (((hasDerivAt_id s).sub_const a).const_mul (highWarpSlope a b ds)).add_const a using 1
  simp

theorem highWarp_lipschitz (a b ds : ℝ) :
    LipschitzWith ‖highWarpSlope a b ds‖₊ (highWarp a b ds) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [highWarp_affine,highWarp_affine,Real.dist_eq,Real.dist_eq]
  have he : highWarpSlope a b ds*(s-a)+a-(highWarpSlope a b ds*(t-a)+a)=
      highWarpSlope a b ds*(s-t) := by ring
  rw [he,abs_mul]
  simp only [coe_nnnorm,Real.norm_eq_abs,le_refl]

theorem highWarp_mem {a b ds s : ℝ} (hab : a<b) (hds : ds<b-a)
    (hs : s∈Icc a b) : highWarp a b ds s∈Icc a (b-ds) := by
  have hj := (highWarpSlope_pos hab hds).le
  constructor
  · rw [highWarp_affine]
    linarith [mul_nonneg hj (sub_nonneg.mpr hs.1)]
  · rw [←highWarp_terminal hab ds,highWarp_affine,highWarp_affine]
    linarith only [mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2 a) hj]

theorem highWarp_maps_inside {a b ds : ℝ} (hab : a<b) (hds : ds<b-a)
    (ha : zStart<a) (hb : b-ds<zEnd) :
    MapsTo (highWarp a b ds) (Icc a b) (Ioo zStart zEnd) := by
  intro s hs
  have hw := highWarp_mem hab hds hs
  exact ⟨ha.trans_le hw.1,hw.2.trans_lt hb⟩

theorem quadratic_antitone_above {lam a z : ℝ} (hla : lam≤a) (haz : a≤z) :
    quadratic lam z≤quadratic lam a := by
  have h := mul_nonneg (sub_nonneg.mpr haz) (show 0≤a+z-2*lam by linarith)
  unfold quadratic
  nlinarith only [h]

theorem transferred_highWarp_deficit_pos {lam delta M a b ds : ℝ}
    {d : LowRankData} {Y : ℝ→ℝ} (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hab : a<b) (hds : ds<b-a) (ha : zStart<a) (hb : b-ds<zEnd)
    (hla : lam+delta≤a) (hM : quadratic (lam+delta) a<M) :
    ∀ s∈Icc a b,0<M-ParameterTransfer.scalar d.S delta-
      T.trajectory (highWarp a b ds s) := by
  intro s hs
  have hw := highWarp_maps_inside hab hds ha hb hs
  have hu := T.upper _ ⟨hw.1.le,hw.2.le⟩
  have hq := quadratic_antitone_above hla (highWarp_mem hab hds hs).1
  linarith

/-- No separate logarithmic positivity or regularity premise is required
once the affine warp endpoints and initial quadratic gap are checked. -/
theorem transferred_highWarp_log_AC {lam delta M a b ds : ℝ}
    {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hab : a<b) (hds : ds<b-a) (ha : zStart<a) (hb : b-ds<zEnd)
    (hla : lam+delta≤a) (hM : quadratic (lam+delta) a<M) :
    AbsolutelyContinuousOnInterval
      (logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory (highWarp a b ds)) a b := by
  apply transferred_logDeficit_AC hd hL hdelta T (highWarp_lipschitz a b ds).lipschitzOnWith
  · rw [uIcc_of_le hab.le]
    intro s hs
    exact ⟨(highWarp_maps_inside hab hds ha hb hs).1.le,
      (highWarp_maps_inside hab hds ha hb hs).2.le⟩
  · rw [uIcc_of_le hab.le]
    exact transferred_highWarp_deficit_pos T hab hds ha hb hla hM

/-- Coarse endpoint boxes suffice for every scalar in the original admissible
range. No optimizer tube is used to justify the logarithmic transformation. -/
theorem highWarp_reference_geometry {lam a b ds : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (ha : a∈Icc (0.783:ℝ) 0.784) (hb : b∈Icc (0.862:ℝ) 0.863)
    (hds : |ds|≤0.005) :
    a<b ∧ ds<b-a ∧ zStart<a ∧ b-ds<zEnd ∧ lam≤a ∧
      quadratic lam a<(0.135:ℝ) ∧ b-ds∈Icc zTest zEnd := by
  have hd := abs_le.mp hds
  have hq := quadratic_antitone_above
    (show lam≤(0.783:ℝ) by linarith [hL.2]) ha.1
  have hmul := mul_le_mul_of_nonneg_right hL.2 (show 0≤(0.783:ℝ) by norm_num)
  have hquad : quadratic lam a<(0.135:ℝ) := by
    unfold quadratic at hq ⊢
    norm_num at hmul ⊢
    linarith
  refine ⟨by linarith [ha.2,hb.1],by linarith [ha.2,hb.1],?_,?_,
    by linarith [hL.2,ha.1],hquad,?_⟩
  · norm_num [zStart]
    linarith [ha.1]
  · norm_num [zEnd]
    linarith [hb.2]
  · constructor <;> norm_num [zTest,zEnd] <;> linarith [hb.1,hb.2]

theorem transferred_scalar_reference_gap {lam delta Sref : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (hSref : Sref∈Icc (0.023:ℝ) 0.024) :
    |ParameterTransfer.scalar d.S delta-Sref|≤(0.005:ℝ) := by
  have hS := ParameterTransfer.shifted_scalar_bounds hd hL hdelta
  norm_num [Certificates.Compact.ScalarRange,Certificates.Compact.scalarLower,
    Certificates.Compact.scalarUpper] at hS
  rw [abs_le]
  constructor <;> linarith [hSref.1,hSref.2]

/-- For either actual reference, the full compact scalar range suffices to
construct the competitor's AC logarithm and its positive deficit. -/
theorem transferred_reference_log_regular {lam delta a b Sref : ℝ}
    {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hL : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (ha : a∈Icc (0.783:ℝ) 0.784) (hb : b∈Icc (0.862:ℝ) 0.863)
    (hSref : Sref∈Icc (0.023:ℝ) 0.024) :
    AbsolutelyContinuousOnInterval
      (logDeficit 0.135 (ParameterTransfer.scalar d.S delta) T.trajectory
        (highWarp a b (ParameterTransfer.scalar d.S delta-Sref))) a b ∧
    (∀ s∈Icc a b,0<(0.135:ℝ)-ParameterTransfer.scalar d.S delta-
      T.trajectory (highWarp a b (ParameterTransfer.scalar d.S delta-Sref) s)) ∧
    b-(ParameterTransfer.scalar d.S delta-Sref)∈Icc zTest zEnd := by
  have hgap := transferred_scalar_reference_gap hd hL hdelta hSref
  obtain ⟨hab,hds,ha',hb',hla,hM,hend⟩ := highWarp_reference_geometry hL ha hb hgap
  exact ⟨transferred_highWarp_log_AC hd hL hdelta T hab hds ha' hb' hla hM,
    transferred_highWarp_deficit_pos T hab hds ha' hb' hla hM,hend⟩

/-- The initial mismatch is the logarithm of the genuine high-rank deficit;
there is no scalar-warp error at the left endpoint. -/
theorem transferred_highWarp_initial_gap {lam delta M a b ds : ℝ}
    {d : LowRankData} {Y : ℝ→ℝ} (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (ha : a∈Icc zStart zEnd) (hM : quadratic (lam+delta) a<M) :
    logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory (highWarp a b ds) a-
      log (M-quadratic (lam+delta) a)=
      log (1+(quadratic (lam+delta) a-ParameterTransfer.scalar d.S delta-T.trajectory a)/
        (M-quadratic (lam+delta) a)) := by
  have hE : 0≤quadratic (lam+delta) a-ParameterTransfer.scalar d.S delta-T.trajectory a := by
    linarith [T.upper a ha]
  have he := logDeficit_initial_gap (sub_pos.mpr hM) hE
  simpa only [logDeficit,highWarp_initial,
    show M-quadratic (lam+delta) a+
      (quadratic (lam+delta) a-ParameterTransfer.scalar d.S delta-T.trajectory a)=
      M-ParameterTransfer.scalar d.S delta-T.trajectory a by ring] using he

end OptimalG.Variational
