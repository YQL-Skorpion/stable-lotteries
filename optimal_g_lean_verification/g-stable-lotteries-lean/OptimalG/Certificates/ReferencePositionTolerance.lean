import OptimalG.Certificates.ReferenceRefinedPosition
import OptimalG.Certificates.ReferenceWeightTolerance

/-! Explicit primary-flow errors for positional-force and flux certificates.
No original tolerance or checker is changed. -/
namespace OptimalG.Certificates.Transport.ReferencePositionCell
open Set

def inputLinkCheckWithError (s multiplier : ℕ) (c : ReferencePositionCell)
    (w : ReferenceWeightCertificate) (error : ℚ) : Bool :=
  decide (c.cell.flow=w.cell.flow ∧ c.exponential=w.cell.exponential.rescale multiplier ∧
    c.terminal=w.cell.terminal.rescale multiplier) &&
  IntegerInterval.centerRadiusCheck (multiplier*s) 0
    error c.flowError

theorem inputLinkCheckWithError_sound {s multiplier : ℕ} (hm : 0<multiplier)
    {c : ReferencePositionCell} {w : ReferenceWeightCertificate} {error : ℚ}
    (hc : c.inputLinkCheckWithError s multiplier w error=true)
    {t E Z terminal : ℝ}
    (hE : w.cell.exponential.Contains s E) (hT : w.cell.terminal.Contains s terminal)
    (herr : |Z-w.cell.flow.valuePolynomial.eval t|≤(error:ℝ)) :
    c.exponential.Contains (multiplier*s) E ∧
    c.terminal.Contains (multiplier*s) terminal ∧
    c.flowError.Contains (multiplier*s) (Z-c.cell.flow.valuePolynomial.eval t) := by
  obtain ⟨hlink,herror⟩ := Bool.and_eq_true_iff.mp hc
  have hl : c.cell.flow=w.cell.flow ∧ c.exponential=w.cell.exponential.rescale multiplier ∧
      c.terminal=w.cell.terminal.rescale multiplier := of_decide_eq_true hlink
  refine ⟨?_,?_,?_⟩
  · rw [hl.2.1]
    exact (IntegerInterval.rescale_contains_iff hm s _ _).mpr hE
  · rw [hl.2.2]
    exact (IntegerInterval.rescale_contains_iff hm s _ _).mpr hT
  · apply IntegerInterval.centerRadiusCheck_sound herror
    simpa only [Rat.cast_zero,sub_zero,hl.1] using herr

theorem checked_linked_force_with_error {s multiplier k : ℕ} (hs : 0<s)
    (hm : 0<multiplier) (hk : 0<k) (c : ReferencePositionCell)
    (w : ReferenceWeightCertificate) (error : ℚ)
    (hc : c.check (multiplier*s) k=true)
    (hl : c.inputLinkCheckWithError s multiplier w error=true)
    {t E Z terminal : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hE : w.cell.exponential.Contains s E) (hT : w.cell.terminal.Contains s terminal)
    (herr : |Z-w.cell.flow.valuePolynomial.eval t|≤(error:ℝ)) :
    c.force.Contains (multiplier*s)
      (E*((RatExpr.partialExpr c.coordinate c.cell.alphaSource).eval (c.cell.frozenInput t)*Z+
        (RatExpr.partialExpr c.coordinate c.cell.betaSource).eval (c.cell.frozenInput t))/terminal) := by
  obtain ⟨he,htm,herror⟩ := inputLinkCheckWithError_sound hm hl hE hT herr
  exact c.checked_force (Nat.mul_pos hm hs) hk hc ht he htm herror

end OptimalG.Certificates.Transport.ReferencePositionCell

namespace OptimalG.Certificates.Transport
open Set

theorem checked_refined_actual_force_with_error {s multiplier k : ℕ}
    (hs : 0<s) (hm : 0<multiplier) (hk : 0<k)
    (c : ReferencePositionCell) (w : ReferenceWeightCertificate) (error : ℚ)
    (hc : c.check (multiplier*s) k=true) (hl : c.inputLinkCheckWithError s multiplier w error=true)
    {start finish lo hi L S : ℚ} {coarse : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish coarse=true) (hmem : parent∈coarse)
    (href : parent.refinementCheck w.cell.flow lo hi=true)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {rate : ℝ} (hrate : 0≤rate)
    (hradius : rate*((w.cell.flow.segment.right.z:ℝ)-start)≤error)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤rate*(z-start))
    {z E terminal : ℝ}
    (hz : z∈Icc (w.cell.flow.segment.left.z:ℝ) w.cell.flow.segment.right.z)
    (hE : w.cell.exponential.Contains s E) (hT : w.cell.terminal.Contains s terminal) :
    c.force.Contains (multiplier*s)
      (E*((RatExpr.partialExpr c.coordinate c.cell.alphaSource).eval
          (c.cell.frozenInput (w.cell.flow.timeParameter z))*Z z+
        (RatExpr.partialExpr c.coordinate c.cell.betaSource).eval
          (c.cell.frozenInput (w.cell.flow.timeParameter z)))/terminal) := by
  have hp := referenceFlowCoverCheck_bounds hcover hmem
  have hg := ReferenceFlowCell.refinement_time_geometry href hp.2.1
  have hwhole : z∈Icc (start:ℝ) finish :=
    ⟨(show (start:ℝ)≤w.cell.flow.segment.left.z by exact_mod_cast hp.1.trans hg.2.1).trans hz.1,
      hz.2.trans (by exact_mod_cast hg.2.2.1.trans hp.2.2)⟩
  have hvalue := refined_polynomial_global hcover hmem href hcurve hpiece hpoly hz
  have herr : |Z z-w.cell.flow.valuePolynomial.eval (w.cell.flow.timeParameter z)|≤
      (error:ℝ) := by
    rw [hvalue]
    exact (herror z hwhole).trans
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2 _) hrate).trans hradius)
  exact ReferencePositionCell.checked_linked_force_with_error hs hm hk c w error hc hl
    (w.cell.flow.timeParameter_mem hg.1 hz) hE hT herr

end OptimalG.Certificates.Transport
