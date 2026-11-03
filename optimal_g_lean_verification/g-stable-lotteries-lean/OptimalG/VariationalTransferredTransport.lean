import OptimalG.VariationalRaisedLogControl
import OptimalG.VariationalTransportSource

/-! The actual transferred trajectory satisfies the integrated logarithmic
comparison. Its differential inequality is derived from the matched support
controls, including the early cap relaxation, rather than assumed separately. -/
namespace OptimalG.Variational
open Set MeasureTheory Real
open scoped NNReal

/-- Either reference branch may be selected measurably in time. The early
branch only needs an upper bound for the primitive; the late branch uses the
exact matching identity. -/
theorem transferred_matched_log_deriv_bound
    {lam delta M s r a R j mR mA xiR xiA : ℝ}
    {d : LowRankData} {Y warp : ℝ → ℝ} {coeff : Fin 4 → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hz : warp s∈Ioo zStart zEnd) (hwarp : HasDerivAt warp j s)
    (hpos : 0<M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s))
    (hj : 0≤j)
    (hbranch :
      (coeff=earlyLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
          (warp s) r a R j mA ∧
        ((r,a,a),mA/xiA,mA/xiA)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r≤R) ∨
      (coeff=lateLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
          (warp s) r a R j mR mA ∧
        ((r,a,r),mA/xiA,mR/xiR)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r=R)) :
    (∑ i,coeff i*exp (-transportDelta i*
      logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp s)/
      transportXi xiR xiA i)≤
      deriv (logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp) s := by
  rw [(transferred_logDeficit_hasDerivAt T hz hwarp hpos).deriv]
  have heq : T.trajectory (warp s)=M-ParameterTransfer.scalar d.S delta-
      (M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s)) := by ring
  rcases hbranch with ⟨hcoeff,hv,hR⟩ | ⟨hcoeff,hv,hR⟩
  · rw [hcoeff]
    exact transferred_early_log_bound_of_primitive_le hd hLnew hdelta T
      ⟨hz.1.le,hz.2.le⟩ hv hR heq hpos hj
  · rw [hcoeff]
    exact transferred_late_log_bound hd hLnew hdelta T
      ⟨hz.1.le,hz.2.le⟩ hv hR heq hpos hj

/-- Full time-integrated entropy comparison for the actual upward-transfer
competitor. Remaining inputs are explicit matched-rank identities, reference
ODE data, and integrability of the three sources subsequently estimated by
finite coefficient and flux certificates. -/
theorem transferred_logarithmic_transport_split
    {lam delta M s0 s1 : ℝ} {d : LowRankData} {Y warp : ℝ → ℝ} {K : ℝ≥0}
    {r a R j mR mA xiR xiA w0 : ℝ → ℝ} {coeff coeff0 : ℝ → Fin 4 → ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hab : s0≤s1) (hwarp : LipschitzOnWith K warp (uIcc s0 s1))
    (hmap : MapsTo warp (uIcc s0 s1) (Icc zStart zEnd))
    (hpos : ∀ s∈uIcc s0 s1,0<M-ParameterTransfer.scalar d.S delta-T.trajectory (warp s))
    (hwarpD : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      warp s∈Ioo zStart zEnd ∧ HasDerivAt warp (j s) s ∧ 0≤j s)
    (hbranch : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      (coeff s=earlyLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
          (warp s) (r s) (a s) (R s) (j s) (mA s) ∧
        ((r s,a s,a s),mA s/xiA s,mA s/xiA s)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta (r s)≤R s) ∨
      (coeff s=lateLogCoefficients (lam+delta) M (ParameterTransfer.scalar d.S delta)
          (warp s) (r s) (a s) (R s) (j s) (mR s) (mA s) ∧
        ((r s,a s,r s),mA s/xiA s,mR s/xiR s)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta (r s)=R s))
    (hw0 : AbsolutelyContinuousOnInterval w0 s0 s1)
    (hpositive : ∀ᵐ s ∂volume.restrict (Icc s0 s1),∀ i,
      ((coeff s i=0 ∧ coeff0 s i=0) ∨ (0<coeff s i ∧ 0<coeff0 s i)) ∧
        0<transportXi (xiR s) (xiA s) i)
    (hw0d : ∀ᵐ s ∂volume.restrict (Icc s0 s1),
      deriv w0 s=∑ i,referenceWeight (coeff0 s i) (transportDelta i) (w0 s))
    (hB : IntervalIntegrable (transportReferenceB coeff0 transportDelta w0) volume s0 s1)
    (hcoef : IntervalIntegrable (transportCoefficientSource
      (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
        w0 coeff coeff0 transportDelta) volume s0 s1)
    (hderiv : IntervalIntegrable (transportDerivativeSource
      (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
        w0 coeff0 (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume s0 s1)
    (hent : IntervalIntegrable (transportEntropySource
      (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
        w0 coeff0 (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume s0 s1) :
    referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0) s0*
      (logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp s0-w0 s0)+
      (∫ s in s0..s1,transportCoefficientSource
        (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
          w0 coeff coeff0 transportDelta s)-
      (∫ s in s0..s1,transportDerivativeSource
        (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
          w0 coeff0 (fun t=>transportXi (xiR t) (xiA t)) transportDelta s)+
      (∫ s in s0..s1,transportEntropySource
        (referenceIntegratingFactor s0 s1 (transportReferenceB coeff0 transportDelta w0))
          w0 coeff0 (fun t=>transportXi (xiR t) (xiA t)) transportDelta s)≤
      logDeficit M (ParameterTransfer.scalar d.S delta) T.trajectory warp s1-w0 s1 := by
  apply logarithmic_transport_split hab
    (transferred_logDeficit_AC hd hLnew hdelta T hwarp hmap hpos) hw0 hpositive
    ?_ hw0d hB hcoef hderiv hent
  filter_upwards [hwarpD,hbranch,ae_restrict_mem measurableSet_Icc] with s hs hc hsi
  exact transferred_matched_log_deriv_bound hd hLnew hdelta T hs.1 hs.2.1
    (hpos s (by simpa only [uIcc_of_le hab] using hsi)) hs.2.2 hc

end OptimalG.Variational
