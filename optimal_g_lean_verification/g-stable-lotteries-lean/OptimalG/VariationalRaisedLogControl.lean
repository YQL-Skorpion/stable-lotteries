import OptimalG.VariationalTransferredLogControl
import OptimalG.VariationalRaisingControl

/-! The early transport branch replaces the competing primitive by its cap.
The original continuation still obeys that relaxed control, even though rank
matching does not provide a primitive equality below the matched interval. -/
namespace OptimalG.Variational
open Set

 theorem transferred_feature_raise_primitive {lam delta z u R : ℝ} {d : LowRankData}
    {Y : ℝ → ℝ} (hd : Admissible lam d)
    (hLnew : Certificates.Compact.LambdaRange (lam+delta)) (hdelta : 0 ≤ delta)
    (T : ParameterTransfer.UpwardTransfer lam delta d Y) (hz : z ∈ Icc zStart zEnd)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hR : ParameterTransfer.shiftedPrimitive lam d delta v.1.1 ≤ R) :
    rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi z u ≤
      Certificates.Control.value (z-(lam+delta)) (2*(lam+delta)-v.1.2.1)
        (v.1.1+v.1.2.2-(lam+delta)) R
        (quadratic (lam+delta) (1-v.1.1)-ParameterTransfer.scalar d.S delta)
        (quadratic (lam+delta) (z-v.1.1)-ParameterTransfer.scalar d.S delta-u) v.2.1 v.2.2 := by
  have hc := (hd.controlFeatureSupport_subset hv).1
  obtain ⟨_,hx,_⟩ := ParameterTransfer.control_ranges hc
  have hscore := hd.rankScoreSupport_bounds (hd.featureSupport_rankScores hv).1
  have hzlo : (0.775 : ℝ) ≤ z := by convert! hz.1 using 1 <;> norm_num [zStart]
  have hU : 0 ≤ z-(lam+delta) := by linarith [hLnew.2]
  have hh : 0 ≤ 2*(lam+delta)-v.1.2.1 := by linarith [hLnew.1,hx.2]
  have hA : v.2.1 ≤ 2*(lam+delta)-v.1.2.1 := by
    have hL := hd.compact_lambdaRange
    linarith [hscore.2.2,hL.1]
  have hP : ParameterTransfer.shiftedPrimitive lam d delta (1-v.1.1)=
      quadratic (lam+delta) (1-v.1.1)-ParameterTransfer.scalar d.S delta := by
    rw [(ParameterTransfer.shifted_control_values lam delta d hc hz).2.1]
    unfold quadratic ParameterTransfer.scalar
    ring
  have hdet := ParameterTransfer.shifted_determinant hd hLnew hdelta hc
  rw [rawDet,hP] at hdet
  have hDp : 0 < Certificates.Control.det (2*(lam+delta)-v.1.2.1)
      (v.1.1+v.1.2.2-(lam+delta)) (ParameterTransfer.shiftedPrimitive lam d delta v.1.1)
      (quadratic (lam+delta) (1-v.1.1)-ParameterTransfer.scalar d.S delta) := by
    unfold Certificates.Control.det
    linarith
  have hraise := Certificates.Control.value_R_raise_clipped (z-(lam+delta))
    (2*(lam+delta)-v.1.2.1) (v.1.1+v.1.2.2-(lam+delta))
    (ParameterTransfer.shiftedPrimitive lam d delta v.1.1) R
    (quadratic (lam+delta) (1-v.1.1)-ParameterTransfer.scalar d.S delta)
    (quadratic (lam+delta) (z-v.1.1)-ParameterTransfer.scalar d.S delta-u) v.2.1 v.2.2 hDp hR hU hh hA
  apply le_trans _ hraise
  apply le_min
  · have hline : rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi z u ≤
        lam+delta-z := min_le_left _ _
    simpa only [neg_sub] using hline
  · have hs := T.support z u v hv
    rwa [transferred_feature_formula hd hLnew hdelta hz hv] at hs

 theorem transferred_early_log_bound_of_primitive_le {lam delta M z r a R j mA xiR xiA Z : ℝ}
    {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0 ≤ delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : z ∈ Icc zStart zEnd)
    (hv : ((r,a,a),mA/xiA,mA/xiA) ∈ controlFeatureSupport d)
    (hR : ParameterTransfer.shiftedPrimitive lam d delta r ≤ R)
    (hZeq : T.trajectory z=M-ParameterTransfer.scalar d.S delta-Z)
    (hZ : 0 < Z) (hj : 0 ≤ j) :
    (∑ i, earlyLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
      z r a R j mA i*Real.exp (-transportDelta i*Real.log Z)/transportXi xiR xiA i) ≤
      -j*rawVectorField (lam+delta) (ParameterTransfer.shiftedPrimitive lam d delta) d.phi
        z (T.trajectory z)/Z := by
  apply early_tested_log_bound hZ hj
  have hh := transferred_feature_raise_primitive hd hLnew hdelta T hz hv hR
    (u:=T.trajectory z)
  dsimp only at hh
  simpa only [hZeq,Certificates.Transport.h,Certificates.Transport.earlyK,
    Certificates.Transport.P,Certificates.quadratic,quadratic] using hh

end OptimalG.Variational
