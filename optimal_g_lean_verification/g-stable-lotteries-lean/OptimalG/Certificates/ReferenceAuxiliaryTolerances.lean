import OptimalG.Certificates.ReferenceAuxiliaryTolerance
import OptimalG.Certificates.ReferenceFlowTolerances

/-! Genuine auxiliary solution with both residual tolerances explicit. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem checked_reference_auxiliary_flow_exists_with_tolerances {a b LX SX LY SY : ℚ} {scale : ℕ}
    {flowResidual auxiliaryResidual : ℤ} {rateX etaAux : ℝ}
    (hscale : 0<scale) (cs : List ReferenceScalarCertificate)
    (hcert : cs.all (fun c=>c.checkWithTolerances scale flowResidual auxiliaryResidual)=true)
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ c∈cs,scalarFor c.cell.flow=c.cell)
    (hcover : referenceFlowCoverCheck a b (cs.map (fun c=>c.cell.flow))=true)
    (hcurveX : trajectoryCheck LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece))=true)
    (hcurveY : trajectoryCheck LY SY (cs.map (·.canonicalAuxiliaryPiece))=true)
    (hpolyX : cs.all (fun c=>c.cell.flow.canonicalPieceCheck)=true)
    (hpolyY : cs.all (·.canonicalAuxiliaryPieceCheck)=true)
    (hzero : auxiliaryInitialZeroCheck cs=true)
    (hlen : (b:ℝ)-a≤2/25) (hrate : 0≤rateX) (heta : 0≤etaAux)
    (haux : (auxiliaryResidual:ℝ)/(scale:ℝ)≤etaAux) {Z : ℝ→ℝ}
    (hZAC : AbsolutelyContinuousOnInterval Z a b)
    (hZ : ∀ z∈Icc (a:ℝ) b,
      |Z z-cubicPrimitive LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece)) z|≤rateX*(z-a)) :
    ∃ V : ℝ→ℝ,V a=0 ∧ AbsolutelyContinuousOnInterval V a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv V z=
        referenceField ReferenceFlowCell.actualAlpha (cs.map (fun c=>c.cell.flow)) z*V z+
          (referenceField (fun f=>(scalarFor f).actualAlphaS) (cs.map (fun c=>c.cell.flow)) z*Z z+
            referenceField (fun f=>(scalarFor f).actualBetaS) (cs.map (fun c=>c.cell.flow)) z)) ∧
      ∀ z∈Icc (a:ℝ) b,|V z-cubicPrimitive LY SY (cs.map (·.canonicalAuxiliaryPiece)) z|≤2*(etaAux+1000*(rateX*((b:ℝ)-a)))*(z-a) := by
  let cells := cs.map (fun c=>c.cell.flow)
  let alpha := referenceField ReferenceFlowCell.actualAlpha cells
  let alphaS := referenceField (fun f=>(scalarFor f).actualAlphaS) cells
  let betaS := referenceField (fun f=>(scalarFor f).actualBetaS) cells
  have hb (c : ReferenceScalarCertificate) (hc : c∈cs) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    c.checked_bounds_with_tolerances hscale (List.all_eq_true.mp hcert c hc) ht
  have halpha : ∀ f∈cells,∀ t∈Icc (0:ℝ) 1,|f.actualAlpha t|≤3 := by
    intro f hf t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hf
    exact (hb c hc t ht).2.2.1
  have halphaS : ∀ f∈cells,∀ t∈Icc (0:ℝ) 1,|(scalarFor f).actualAlphaS t|≤1000 := by
    intro f hf t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hf
    rw [hscalar c hc]
    exact (hb c hc t ht).2.2.2.2.1
  have hbetaS : ∀ f∈cells,∀ t∈Icc (0:ℝ) 1,|(scalarFor f).actualBetaS t|≤100000 := by
    intro f hf t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hf
    rw [hscalar c hc]
    exact (hb c hc t ht).2.2.2.2.2
  have hab := referenceFlowCoverCheck_order hcover
  have hab' : (a:ℝ)≤b := by exact_mod_cast hab
  have hAlpha : IntervalIntegrable alpha volume a b := referenceField_intervalIntegrable _ hab
    hcover ReferenceFlowCell.actualAlpha_measurable halpha
  have hAlphaS : IntervalIntegrable alphaS volume a b := referenceField_intervalIntegrable _ hab
    hcover (fun f=>(scalarFor f).actualAlphaS_measurable) halphaS
  have hBetaS : IntervalIntegrable betaS volume a b := referenceField_intervalIntegrable _ hab
    hcover (fun f=>(scalarFor f).actualBetaS_measurable) hbetaS
  have hForce : IntervalIntegrable (fun z=>alphaS z*Z z+betaS z) volume a b :=
    (hAlphaS.mul_continuousOn hZAC.continuousOn).add hBetaS
  obtain ⟨V,hinit,hAC,hder⟩ := Variational.exists_affine_reference_solution (x0:=0) hAlpha hForce
  have hder' : ∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv V z=alpha z*V z+(alphaS z*Z z+betaS z) := by
    filter_upwards [ae_restrict_of_ae hder,self_mem_ae_restrict measurableSet_Icc] with z hd hz
    exact (hd (by simpa only [uIcc_of_le hab'] using hz)).deriv
  refine ⟨V,hinit,hAC,hder',?_⟩
  apply reference_sensitivity_enclosed_with_tolerance hab' hlen
    heta (by norm_num) hrate hAlpha (trajectoryCheck_hasDerivAt LY SY _ hcurveY)
    (trajectoryCheck_continuousScore LY SY _ hcurveY) hAC
    ((checked_auxiliary_initial_zero hcover hcurveY hpolyY hzero).trans hinit.symm) hder'
  · apply ae_Icc_of_forall_Ioc
    intro z hz
    exact (le_abs_self _).trans (referenceField_bounded _ hcover halpha hz)
  · apply ae_Icc_of_forall_Ioc
    intro z hz
    exact referenceField_bounded _ hcover halphaS hz
  · exact hZ
  · apply reference_auxiliary_curve_residual scalarFor hscalar hcover hcurveX hcurveY hpolyX hpolyY
    intro c hc t ht
    exact (hb c hc t ht).2.1.trans haux

end OptimalG.Certificates.Transport
