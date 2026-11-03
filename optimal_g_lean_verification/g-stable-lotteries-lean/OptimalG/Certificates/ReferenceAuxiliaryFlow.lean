import OptimalG.Certificates.ReferenceCheckedFlow
import OptimalG.Certificates.ReferenceSensitivityComparison
import OptimalG.VariationalAffineFirstVariation

/-! A finite certificate list constructs the actual auxiliary affine ODE.
The checked cubic is only an enclosure; the solution is constructed by the
integrating factor with the actual scalar derivatives of the coefficients. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

namespace ReferenceScalarCell

theorem actualAlphaS_measurable (c : ReferenceScalarCell) : Measurable c.actualAlphaS := by
  have h := RatExpr.measurable_evalOne c.alphaSExpr
  convert h using 1
  funext t
  exact (c.alphaSExpr_eval t).symm

theorem actualBetaS_measurable (c : ReferenceScalarCell) : Measurable c.actualBetaS := by
  have h := RatExpr.measurable_evalOne c.betaSExpr
  convert h using 1
  funext t
  exact (c.betaSExpr_eval t).symm

end ReferenceScalarCell

namespace ReferenceScalarCertificate

def canonicalAuxiliaryPiece (c : ReferenceScalarCertificate) : CubicPiece :=
  ⟨c.cell.flow.segment.left.z,c.cell.flow.segment.right.z,
    c.polynomial[1]?.getD 0/c.cell.flow.length,
    2*c.polynomial[2]?.getD 0/c.cell.flow.length^2,
    3*c.polynomial[3]?.getD 0/c.cell.flow.length^3,
    0,c.polynomial[0]?.getD 0⟩

def canonicalAuxiliaryPieceCheck (c : ReferenceScalarCertificate) : Bool :=
  polynomialPieceCheck c.polynomial c.cell.flow.segment.left.z
    c.cell.flow.segment.right.z c.canonicalAuxiliaryPiece

end ReferenceScalarCertificate

def auxiliaryInitialZeroCheck : List ReferenceScalarCertificate → Bool
  | [] => false
  | c::_ => decide (c.polynomial[0]?.getD 0=0)

private theorem polynomial_eval_zero (p : RationalPolynomial) :
    p.eval 0=((p[0]?.getD 0:ℚ):ℝ) := by
  cases p <;> simp [RationalPolynomial.eval]

theorem checked_auxiliary_initial_zero {a b L S : ℚ}
    {cs : List ReferenceScalarCertificate}
    (hcover : referenceFlowCoverCheck a b (cs.map (fun c=>c.cell.flow))=true)
    (hcurve : trajectoryCheck L S (cs.map (·.canonicalAuxiliaryPiece))=true)
    (hpoly : cs.all (·.canonicalAuxiliaryPieceCheck)=true)
    (hzero : auxiliaryInitialZeroCheck cs=true) :
    cubicPrimitive L S (cs.map (·.canonicalAuxiliaryPiece)) a=0 := by
  cases cs with
  | nil => simp [auxiliaryInitialZeroCheck] at hzero
  | cons c cs =>
    have hfirst : c.cell.flow.segment.left.z=a ∧
        c.cell.flow.segment.left.z<c.cell.flow.segment.right.z :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hcover).1
    have hpolyC := List.all_eq_true.mp hpoly c List.mem_cons_self
    have hmem : c.canonicalAuxiliaryPiece∈(c::cs).map (·.canonicalAuxiliaryPiece) :=
      List.mem_map.mpr ⟨c,List.mem_cons_self,rfl⟩
    have hcont := continuous_iff_continuousAt.mpr (fun z=>
      (trajectoryCheck_hasDerivAt L S _ hcurve z).continuousAt)
    have hv := polynomialPieceCheck_global hpolyC hfirst.2
      (trajectoryCheck_lookup hcurve hmem) (trajectoryCheck_continuousScore L S _ hcurve)
      hcont (z:=(a:ℝ)) (by
        constructor
        · rw [hfirst.1]
        · exact_mod_cast hfirst.1 ▸ hfirst.2.le)
    have hz : c.polynomial[0]?.getD 0=0 := of_decide_eq_true hzero
    rw [hfirst.1,sub_self,zero_div,polynomial_eval_zero,hz,Rat.cast_zero] at hv
    exact hv.1.symm

theorem reference_auxiliary_curve_residual {a b LX SX LY SY : ℚ}
    {cs : List ReferenceScalarCertificate}
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ c∈cs,scalarFor c.cell.flow=c.cell)
    (hcover : referenceFlowCoverCheck a b (cs.map (fun c=>c.cell.flow))=true)
    (hcurveX : trajectoryCheck LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece))=true)
    (hcurveY : trajectoryCheck LY SY (cs.map (·.canonicalAuxiliaryPiece))=true)
    (hpolyX : cs.all (fun c=>c.cell.flow.canonicalPieceCheck)=true)
    (hpolyY : cs.all (·.canonicalAuxiliaryPieceCheck)=true)
    {eta : ℝ}
    (hresidual : ∀ c∈cs,∀ t∈Icc (0:ℝ) 1,
      |c.polynomial.derivative.eval t/(c.cell.flow.length:ℝ)-
        c.cell.flow.actualAlpha t*c.polynomial.eval t-
        c.cell.actualAlphaS t*c.cell.flow.valuePolynomial.eval t-c.cell.actualBetaS t|≤eta) :
    ∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),
      |cubicScore LY (cs.map (·.canonicalAuxiliaryPiece)) z-
        referenceField ReferenceFlowCell.actualAlpha (cs.map (fun c=>c.cell.flow)) z*
          cubicPrimitive LY SY (cs.map (·.canonicalAuxiliaryPiece)) z-
        referenceField (fun f=>(scalarFor f).actualAlphaS) (cs.map (fun c=>c.cell.flow)) z*
          cubicPrimitive LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece)) z-
        referenceField (fun f=>(scalarFor f).actualBetaS) (cs.map (fun c=>c.cell.flow)) z|≤eta := by
  have hcontX := continuous_iff_continuousAt.mpr (fun z=>
    (trajectoryCheck_hasDerivAt LX SX _ hcurveX z).continuousAt)
  have hcontY := continuous_iff_continuousAt.mpr (fun z=>
    (trajectoryCheck_hasDerivAt LY SY _ hcurveY z).continuousAt)
  apply ae_Icc_of_forall_Ioc
  intro z hz
  obtain ⟨f,hf,hpos,hzf,hAlpha⟩ := referenceField_selected ReferenceFlowCell.actualAlpha hcover hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hf
  have hmemX : c.cell.flow.canonicalPiece∈cs.map (fun c=>c.cell.flow.canonicalPiece) :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  have hmemY : c.canonicalAuxiliaryPiece∈cs.map (·.canonicalAuxiliaryPiece) :=
    List.mem_map.mpr ⟨c,hc,rfl⟩
  have hx := polynomialPieceCheck_global (List.all_eq_true.mp hpolyX c hc) hpos
    (trajectoryCheck_lookup hcurveX hmemX) (trajectoryCheck_continuousScore LX SX _ hcurveX)
    hcontX ⟨hzf.1.le,hzf.2⟩
  have hy := polynomialPieceCheck_global (List.all_eq_true.mp hpolyY c hc) hpos
    (trajectoryCheck_lookup hcurveY hmemY) (trajectoryCheck_continuousScore LY SY _ hcurveY)
    hcontY ⟨hzf.1.le,hzf.2⟩
  have hmem : c.cell.flow∈cs.map (fun c=>c.cell.flow) := List.mem_map.mpr ⟨c,hc,rfl⟩
  rw [hAlpha,referenceField_on_cell (fun f=>(scalarFor f).actualAlphaS) hcover hmem hzf,
    referenceField_on_cell (fun f=>(scalarFor f).actualBetaS) hcover hmem hzf,hscalar c hc,
    ←hx.1,←hy.1,←hy.2]
  simpa only [ReferenceFlowCell.timeParameter,ReferenceFlowCell.length,Rat.cast_sub] using
    hresidual c hc _ (c.cell.flow.timeParameter_mem hpos ⟨hzf.1.le,hzf.2⟩)

theorem checked_reference_auxiliary_flow_exists {a b LX SX LY SY : ℚ} {scale : ℕ}
    (hscale : 0<scale) (cs : List ReferenceScalarCertificate)
    (hcert : cs.all (fun c=>c.check scale)=true)
    (scalarFor : ReferenceFlowCell→ReferenceScalarCell)
    (hscalar : ∀ c∈cs,scalarFor c.cell.flow=c.cell)
    (hcover : referenceFlowCoverCheck a b (cs.map (fun c=>c.cell.flow))=true)
    (hcurveX : trajectoryCheck LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece))=true)
    (hcurveY : trajectoryCheck LY SY (cs.map (·.canonicalAuxiliaryPiece))=true)
    (hpolyX : cs.all (fun c=>c.cell.flow.canonicalPieceCheck)=true)
    (hpolyY : cs.all (·.canonicalAuxiliaryPieceCheck)=true)
    (hzero : auxiliaryInitialZeroCheck cs=true)
    (hlen : (b:ℝ)-a≤2/25) {Z : ℝ→ℝ}
    (hZAC : AbsolutelyContinuousOnInterval Z a b)
    (hZ : ∀ z∈Icc (a:ℝ) b,
      |Z z-cubicPrimitive LX SX (cs.map (fun c=>c.cell.flow.canonicalPiece)) z|≤(z-a)/2500000000) :
    ∃ V : ℝ→ℝ,V a=0 ∧ AbsolutelyContinuousOnInterval V a b ∧
      (∀ᵐ z ∂volume.restrict (Icc (a:ℝ) b),deriv V z=
        referenceField ReferenceFlowCell.actualAlpha (cs.map (fun c=>c.cell.flow)) z*V z+
          (referenceField (fun f=>(scalarFor f).actualAlphaS) (cs.map (fun c=>c.cell.flow)) z*Z z+
            referenceField (fun f=>(scalarFor f).actualBetaS) (cs.map (fun c=>c.cell.flow)) z)) ∧
      ∀ z∈Icc (a:ℝ) b,|V z-cubicPrimitive LY SY (cs.map (·.canonicalAuxiliaryPiece)) z|≤(z-a)/250000 := by
  let cells := cs.map (fun c=>c.cell.flow)
  let alpha := referenceField ReferenceFlowCell.actualAlpha cells
  let alphaS := referenceField (fun f=>(scalarFor f).actualAlphaS) cells
  let betaS := referenceField (fun f=>(scalarFor f).actualBetaS) cells
  have hb (c : ReferenceScalarCertificate) (hc : c∈cs) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :=
    c.checked_bounds hscale (List.all_eq_true.mp hcert c hc) ht
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
  apply reference_sensitivity_enclosed hlen hAlpha (trajectoryCheck_hasDerivAt LY SY _ hcurveY)
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
    apply (hb c hc t ht).2.1.trans
    have hn := Nat.div_mul_le_self scale 400000
    have hr : ((scale/400000:ℕ):ℝ)*400000≤(scale:ℝ) := by exact_mod_cast hn
    apply (div_le_iff₀ (show (0:ℝ)<scale by exact_mod_cast hscale)).mpr
    linarith only [hr]

end OptimalG.Certificates.Transport
