import OptimalG.Certificates.ReferenceLogSemantics
import OptimalG.VariationalTransferredTransport
import OptimalG.VariationalHighWarp

/-! The logarithmic transport inequality uses the actual transferred
continuation and the actual reference affine ODE. The affine warp, reference
log derivative and integrating factor are derived here; finite coefficient
and rank-source bounds enter only through their ordinary integrability. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory Real Variational

theorem transferred_reference_flow
    {lam delta Sref : ℝ} {d : LowRankData} {Y Z rho : ℝ→ℝ}
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    {r a R mR mA xiR xiA : ℝ→ℝ} {coeff : ℝ→Fin 4→ℝ}
    (hd : Admissible lam d) (hL : Compact.LambdaRange (lam+delta))
    (hdelta : 0≤delta) (T : ParameterTransfer.UpwardTransfer lam delta d Y)
    (hstart : (start:ℝ)∈Icc (0.783:ℝ) 0.784)
    (hfinish : (finish:ℝ)∈Icc (0.862:ℝ) 0.863)
    (hSref : Sref∈Icc (0.023:ℝ) 0.024)
    (hcover : referenceFlowCoverCheck start finish cells=true)
    (hZ : AbsolutelyContinuousOnInterval Z start finish)
    (hZpos : ∀ z∈Icc (start:ℝ) finish,0<Z z)
    (hZd : ∀ᵐ z ∂volume.restrict (Icc (start:ℝ) finish),
      deriv Z z=referenceField ReferenceFlowCell.actualAlpha cells z*Z z+
        referenceField ReferenceFlowCell.actualBeta cells z)
    (hbeta : IntervalIntegrable (referenceField ReferenceFlowCell.actualBeta cells)
      volume (start:ℝ) finish)
    (hrho : ∀ z∈Icc (start:ℝ) finish,rho z=
      referenceIntegratingFactor start finish
        (fun s=>referenceField ReferenceFlowCell.actualBeta cells s/Z s) z)
    (hbranch : ∀ᵐ s ∂volume.restrict (Icc (start:ℝ) finish),
      (coeff s=earlyLogCoefficients (lam+delta) 0.135 (ParameterTransfer.scalar d.S delta)
          (highWarp start finish (ParameterTransfer.scalar d.S delta-Sref) s)
          (r s) (a s) (R s) (highWarpSlope start finish
            (ParameterTransfer.scalar d.S delta-Sref)) (mA s) ∧
        ((r s,a s,a s),mA s/xiA s,mA s/xiA s)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta (r s)≤R s) ∨
      (coeff s=lateLogCoefficients (lam+delta) 0.135 (ParameterTransfer.scalar d.S delta)
          (highWarp start finish (ParameterTransfer.scalar d.S delta-Sref) s)
          (r s) (a s) (R s) (highWarpSlope start finish
            (ParameterTransfer.scalar d.S delta-Sref)) (mR s) (mA s) ∧
        ((r s,a s,r s),mA s/xiA s,mR s/xiR s)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta (r s)=R s))
    (hpositive : ∀ᵐ s ∂volume.restrict (Icc (start:ℝ) finish),∀ i,
      ((coeff s i=0 ∧ referenceCoefficient cells i s=0) ∨
        (0<coeff s i ∧ 0<referenceCoefficient cells i s)) ∧
        0<transportXi (xiR s) (xiA s) i)
    (hcoef : IntervalIntegrable (transportCoefficientSource rho (fun s=>log (Z s))
      coeff (fun s i=>referenceCoefficient cells i s) transportDelta)
        volume (start:ℝ) finish)
    (hderiv : IntervalIntegrable (transportDerivativeSource rho (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume (start:ℝ) finish)
    (hent : IntervalIntegrable (transportEntropySource rho (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume (start:ℝ) finish) :
    rho start*(logDeficit 0.135 (ParameterTransfer.scalar d.S delta) T.trajectory
        (highWarp start finish (ParameterTransfer.scalar d.S delta-Sref)) start-log (Z start))+
      (∫ s in (start:ℝ)..finish,transportCoefficientSource rho (fun s=>log (Z s))
        coeff (fun s i=>referenceCoefficient cells i s) transportDelta s)-
      (∫ s in (start:ℝ)..finish,transportDerivativeSource rho (fun s=>log (Z s))
        (fun s i=>referenceCoefficient cells i s)
        (fun s=>transportXi (xiR s) (xiA s)) transportDelta s)+
      (∫ s in (start:ℝ)..finish,transportEntropySource rho (fun s=>log (Z s))
        (fun s i=>referenceCoefficient cells i s)
        (fun s=>transportXi (xiR s) (xiA s)) transportDelta s)≤
      logDeficit 0.135 (ParameterTransfer.scalar d.S delta) T.trajectory
        (highWarp start finish (ParameterTransfer.scalar d.S delta-Sref)) finish-log (Z finish) := by
  let ds := ParameterTransfer.scalar d.S delta-Sref
  have hgap := transferred_scalar_reference_gap hd hL hdelta hSref
  obtain ⟨hab,hds,ha',hb',hla,hM,_⟩ := highWarp_reference_geometry hL hstart hfinish hgap
  have hw0 := reference_log_derivative hcover hZ hZpos hZd
  have hB := reference_transport_B_integrable hcover hbeta hZ hZpos
  let rr := referenceIntegratingFactor start finish
    (transportReferenceB (fun s i=>referenceCoefficient cells i s) transportDelta
      (fun s=>log (Z s)))
  have heq (s : ℝ) (hs : s∈Icc (start:ℝ) finish) : rr s=rho s :=
    (reference_transport_adjoint hcover hZpos hs).trans (hrho s hs).symm
  have hiCoeff : IntervalIntegrable (transportCoefficientSource rr (fun s=>log (Z s))
      coeff (fun s i=>referenceCoefficient cells i s) transportDelta) volume (start:ℝ) finish := by
    apply hcoef.congr_uIoo
    rw [uIoo_of_le hab.le]
    intro s hs
    simp only [transportCoefficientSource,heq s ⟨hs.1.le,hs.2.le⟩]
  have hiDeriv : IntervalIntegrable (transportDerivativeSource rr (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume (start:ℝ) finish := by
    apply hderiv.congr_uIoo
    rw [uIoo_of_le hab.le]
    intro s hs
    simp only [transportDerivativeSource,heq s ⟨hs.1.le,hs.2.le⟩]
  have hiEntropy : IntervalIntegrable (transportEntropySource rr (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta) volume (start:ℝ) finish := by
    apply hent.congr_uIoo
    rw [uIoo_of_le hab.le]
    intro s hs
    simp only [transportEntropySource,heq s ⟨hs.1.le,hs.2.le⟩]
  have hh := transferred_logarithmic_transport_split hd hL hdelta T hab.le
    (highWarp_lipschitz start finish ds).lipschitzOnWith
    (by
      rw [uIcc_of_le hab.le]
      intro s hs
      have hz := highWarp_maps_inside hab hds ha' hb' hs
      exact ⟨hz.1.le,hz.2.le⟩)
    (by
      rw [uIcc_of_le hab.le]
      exact transferred_highWarp_deficit_pos T hab hds ha' hb' hla hM)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ⟨highWarp_maps_inside hab hds ha' hb' hs,
        highWarp_hasDerivAt start finish ds s,(highWarpSlope_pos hab hds).le⟩)
    hbranch hw0.1 hpositive hw0.2 hB hiCoeff hiDeriv hiEntropy
  have eCoeff : (∫ s in (start:ℝ)..finish,transportCoefficientSource rr (fun s=>log (Z s))
      coeff (fun s i=>referenceCoefficient cells i s) transportDelta s)=
      ∫ s in (start:ℝ)..finish,transportCoefficientSource rho (fun s=>log (Z s))
        coeff (fun s i=>referenceCoefficient cells i s) transportDelta s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    simp only [transportCoefficientSource,heq s ⟨hs.1.le,hs.2.le⟩]
  have eDeriv : (∫ s in (start:ℝ)..finish,transportDerivativeSource rr (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta s)=
      ∫ s in (start:ℝ)..finish,transportDerivativeSource rho (fun s=>log (Z s))
        (fun s i=>referenceCoefficient cells i s)
        (fun s=>transportXi (xiR s) (xiA s)) transportDelta s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    simp only [transportDerivativeSource,heq s ⟨hs.1.le,hs.2.le⟩]
  have eEntropy : (∫ s in (start:ℝ)..finish,transportEntropySource rr (fun s=>log (Z s))
      (fun s i=>referenceCoefficient cells i s)
      (fun s=>transportXi (xiR s) (xiA s)) transportDelta s)=
      ∫ s in (start:ℝ)..finish,transportEntropySource rho (fun s=>log (Z s))
        (fun s i=>referenceCoefficient cells i s)
        (fun s=>transportXi (xiR s) (xiA s)) transportDelta s := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    simp only [transportEntropySource,heq s ⟨hs.1.le,hs.2.le⟩]
  change rr start*(_-_)+_-_+_≤_ at hh
  rw [heq start ⟨le_rfl,hab.le⟩,eCoeff,eDeriv,eEntropy] at hh
  exact hh

end OptimalG.Certificates.Transport
