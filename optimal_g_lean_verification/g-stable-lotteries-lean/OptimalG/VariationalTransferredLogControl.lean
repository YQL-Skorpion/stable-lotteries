import OptimalG.VariationalTransferredMatching
import OptimalG.VariationalMatchedSupports
import OptimalG.VariationalTransportTerms
import OptimalG.VariationalLogRegularity

/-! The actual upward-transfer trajectory satisfies the transformed early and
late logarithmic control inequalities. This connects rank matching and the
reference coefficient formulas to the original continuation, not to a separately
postulated auxiliary flow. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

 theorem transferred_feature_formula {lam delta z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (hz : z ∈ Icc zStart zEnd)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    rawFeatureH (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) z u v=
      Certificates.Control.value (z-(lam+delta)) (2*(lam+delta)-v.1.2.1)
        (v.1.1+v.1.2.2-(lam+delta))
        (ParameterTransfer.shiftedPrimitive lam d delta v.1.1)
        (quadratic (lam+delta) (1-v.1.1)-ParameterTransfer.scalar d.S delta)
        (quadratic (lam+delta) (z-v.1.1)-ParameterTransfer.scalar d.S delta-u) v.2.1 v.2.2 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  obtain ⟨_,hP,hK⟩ := ParameterTransfer.shifted_control_values lam delta d hc hz
  rw [rawFeatureH_eq_value z u v (ParameterTransfer.shifted_determinant hd hLnew hdelta hc),hP,hK]
  unfold quadratic ParameterTransfer.scalar
  congr 1 <;> ring

 theorem transferred_logDeficit_hasDerivAt {lam delta M s j : ℝ} {d : LowRankData}
    {Y warp : ℝ → ℝ} (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : warp s ∈ Ioo zStart zEnd) (hwarp : HasDerivAt warp j s)
    (hpos : 0 < M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s)) :
    HasDerivAt (logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp)
      (-j*rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi
        (warp s) (T.trajectory (warp s))/
        (M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s))) s := by
  have hY := (T.derivative (warp s) ⟨hz.1.le,hz.2.le⟩).hasDerivAt
    (Icc_mem_nhds hz.1 hz.2)
  exact logDeficit_hasDerivAt hY hwarp hpos

 theorem transferred_logDeficit_AC {lam delta M a b : ℝ} {d : LowRankData}
    {Y warp : ℝ → ℝ} {K : ℝ≥0}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hwarp : LipschitzOnWith K warp (uIcc a b))
    (hmap : MapsTo warp (uIcc a b) (Icc zStart zEnd))
    (hpos : ∀ s ∈ uIcc a b, 0 < M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s)) :
    AbsolutelyContinuousOnInterval
      (logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp) a b := by
  obtain ⟨K',hK',htime⟩ := ParameterTransfer.shifted_regular hd hLnew hdelta
  obtain ⟨L,hL⟩ := continuous_ode_solution_lipschitz hK' (htime 0).continuousOn T.derivative
  exact logDeficit_AC_of_lipschitz hL hwarp hmap hpos

 theorem transferred_late_log_bound {lam delta M z r a R j mR mA xiR xiA Z : ℝ}
    {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : z ∈ Icc zStart zEnd)
    (hv : ((r,a,r),mA/xiA,mR/xiR) ∈ controlFeatureSupport d)
    (hR : ParameterTransfer.shiftedPrimitive lam d delta r=R)
    (hZeq : T.trajectory z=M-ParameterTransfer.scalar d.S delta-Z)
    (hZ : 0 < Z) (hj : 0 ≤ j) :
    (∑ i, lateLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
      z r a R j mR mA i*Real.exp (-transportDelta i*Real.log Z)/transportXi xiR xiA i) ≤
      -j*rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi
        z (T.trajectory z)/Z := by
  apply late_tested_log_bound hZ hj
  have hh := T.support z (T.trajectory z) _ hv
  rw [transferred_feature_formula hd hLnew hdelta hz hv] at hh
  dsimp only at hh
  rw [hR,hZeq] at hh
  convert! hh using 1 <;> simp only [hZeq,Certificates.Transport.h,
    Certificates.Transport.earlyK,Certificates.Transport.lateK,Certificates.Transport.P,
    Certificates.quadratic,quadratic] <;> congr 1 <;> ring

 theorem transferred_early_log_bound {lam delta M z r a R j mA xiR xiA Z : ℝ}
    {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : z ∈ Icc zStart zEnd)
    (hv : ((r,a,a),mA/xiA,mA/xiA) ∈ controlFeatureSupport d)
    (hR : ParameterTransfer.shiftedPrimitive lam d delta r=R)
    (hZeq : T.trajectory z=M-ParameterTransfer.scalar d.S delta-Z)
    (hZ : 0 < Z) (hj : 0 ≤ j) :
    (∑ i, earlyLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
      z r a R j mA i*Real.exp (-transportDelta i*Real.log Z)/transportXi xiR xiA i) ≤
      -j*rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi
        z (T.trajectory z)/Z := by
  apply early_tested_log_bound hZ hj
  have hh := T.support z (T.trajectory z) _ hv
  rw [transferred_feature_formula hd hLnew hdelta hz hv] at hh
  dsimp only at hh
  rw [hR,hZeq] at hh
  convert! hh using 1 <;> simp only [hZeq,Certificates.Transport.h,
    Certificates.Transport.earlyK,Certificates.Transport.lateK,Certificates.Transport.P,
    Certificates.quadratic,quadratic] <;> congr 1 <;> ring

end OptimalG.Variational
