import OptimalG.Certificates.ReferenceRefinedWeights
import OptimalG.Certificates.ReferenceValueTolerance

/-! Reference-weight certificates with an explicit primary-flow error.
The original certificate interface and its tighter tolerance are unchanged. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory
namespace ReferenceWeightCertificate

def checkWithError (s k : ℕ) (c : ReferenceWeightCertificate) (error : ℚ) : Bool :=
  c.cell.flow.alphaExpr.midpointScaledIntegralCheck s k c.cell.flow.length c.mean c.mass &&
  c.cell.flow.alphaExpr.cleanup.enclosureRefinedCheck s k (fun _ => ⟨0,s⟩) c.alphaBounds &&
  c.cell.flow.actualValueCheckWithError s k error c.cell.deficit && c.cell.check s k

theorem checked_integral_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true) :
    c.mass.Contains s ((c.cell.flow.length:ℝ)*
      (∫ t in (0:ℝ)..1,c.cell.flow.actualAlpha t)) := by
  have hh := hc
  simp only [checkWithError,Bool.and_eq_true] at hh
  have h := RatExpr.midpointScaledIntegralCheck_sound hs hk c.cell.flow.alphaExpr
    c.cell.flow.length c.mean c.mass hh.1.1.1
  simpa only [ReferenceFlowCell.alphaExpr_eval] using h

theorem checked_alpha_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : c.alphaBounds.Contains s (c.cell.flow.actualAlpha t) := by
  have hh := hc
  simp only [checkWithError,Bool.and_eq_true] at hh
  have hu : ∀ i : Fin 1,(⟨0,(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro i
    exact ⟨by simpa using (mul_nonneg (show (0:ℝ)≤s by positivity) ht.1),
      by simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)⟩
  have h := RatExpr.enclosureRefinedCheck_sound hs hk c.cell.flow.alphaExpr.cleanup
    (fun _ => ⟨0,s⟩) c.alphaBounds hh.1.1.2 (fun _ => t) hu
  rw [RatExpr.cleanup_eval] at h
  change c.alphaBounds.Contains s (c.cell.flow.alphaExpr.evalOne t) at h
  rwa [ReferenceFlowCell.alphaExpr_eval] at h

theorem checked_weights_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {t exponent Z terminal : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (he : c.cell.exponent.Contains s exponent)
    (herror : |Z-c.cell.flow.valuePolynomial.eval t|≤(error:ℝ))
    (hterm : c.cell.terminal.Contains s terminal) (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Real.exp exponent*(c.cell.flow.baseCoefficientExpr i).evalOne t*
        (if i<2 then Z else 1)/terminal) := by
  have hh := hc
  simp only [checkWithError,Bool.and_eq_true] at hh
  exact c.cell.checked_weights hs hk hh.2 ht he
    (c.cell.flow.actualValueCheckWithError_sound hs hk error c.cell.deficit hh.1.2 ht herror)
    hterm i

end ReferenceWeightCertificate

theorem checked_refined_alpha_mass_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {start finish lo hi : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) :
    c.mass.Contains s (∫ z in (c.cell.flow.segment.left.z:ℝ)..c.cell.flow.segment.right.z,
      referenceField ReferenceFlowCell.actualAlpha cells z) := by
  rw [referenceField_refined_alpha_integral hcover hmem href]
  exact c.checked_integral_with_error hs hk error hc

theorem checked_refined_alpha_bound_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {start finish lo hi : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true) :
    ∀ᵐ z ∂volume.restrict (Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z),
      c.alphaBounds.Contains s (referenceField ReferenceFlowCell.actualAlpha cells z) := by
  apply ae_Icc_of_forall_Ioc
  intro z hz
  rw [(referenceField_on_refined_cell hcover hmem href hz).1]
  have hpos := (ReferenceFlowCell.refinement_time_geometry href
    (referenceFlowCoverCheck_bounds hcover hmem).2.1).1
  exact c.checked_alpha_with_error hs hk error hc (c.cell.flow.timeParameter_mem hpos ⟨hz.1.le,hz.2⟩)


/-- The widened weight box encloses the genuine global flow, using the
proved global error rate and the exact refinement identity. -/
theorem checked_refined_actual_weights_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (error : ℚ) (hc : c.checkWithError s k error=true)
    {start finish lo hi L S : ℚ} {cells : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish cells=true) (hmem : parent∈cells)
    (href : parent.refinementCheck c.cell.flow lo hi=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {rate : ℝ} (hrate : 0≤rate)
    (hradius : rate*((c.cell.flow.segment.right.z:ℝ)-start)≤error)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤rate*(z-start))
    {z exponent terminal : ℝ}
    (hz : z∈Icc (c.cell.flow.segment.left.z:ℝ) c.cell.flow.segment.right.z)
    (he : c.cell.exponent.Contains s exponent) (hT : c.cell.terminal.Contains s terminal)
    (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Real.exp exponent*(c.cell.flow.baseCoefficientExpr i).evalOne (c.cell.flow.timeParameter z)*
        (if i<2 then Z z else 1)/terminal) := by
  have hparent := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hparent.2.1
  have hwhole : z∈Icc (start:ℝ) finish :=
    ⟨(show (start:ℝ)≤c.cell.flow.segment.left.z by exact_mod_cast hparent.1.trans hg.2.1).trans hz.1,
      hz.2.trans (by exact_mod_cast hg.2.2.1.trans hparent.2.2)⟩
  have hvalue := refined_polynomial_global hcover hmem href hcurve hpiece hpoly hz
  have herr : |Z z-c.cell.flow.valuePolynomial.eval (c.cell.flow.timeParameter z)|≤(error:ℝ) := by
    rw [hvalue]
    exact (herror z hwhole).trans
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2 _) hrate).trans hradius)
  exact c.checked_weights_with_error hs hk error hc
    (c.cell.flow.timeParameter_mem hg.1 hz) he herr hT i

end OptimalG.Certificates.Transport
