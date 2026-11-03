import OptimalG.Certificates.ReferencePositionLink

/-! The positional-force interval is evaluated on the actual enclosed
reference solution. Its local polynomial error is derived from the global
ODE comparison and the accepted affine subdivision identities. -/
namespace OptimalG.Certificates.Transport
open Set

theorem checked_refined_actual_force {s multiplier k : ℕ}
    (hs : 0<s) (hm : 0<multiplier) (hk : 0<k)
    (c : ReferencePositionCell) (w : ReferenceWeightCertificate)
    (hc : c.check (multiplier*s) k=true) (hl : c.inputLinkCheck s multiplier w=true)
    {start finish lo hi L S : ℚ} {coarse : List ReferenceFlowCell} {parent : ReferenceFlowCell}
    {pieces : List CubicPiece}
    (hcover : referenceFlowCoverCheck start finish coarse=true) (hmem : parent∈coarse)
    (href : parent.refinementCheck w.cell.flow lo hi=true) (hstart : w.start=start)
    (hcurve : trajectoryCheck L S pieces=true)
    (hpiece : parent.canonicalPiece∈pieces) (hpoly : parent.canonicalPieceCheck=true)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S pieces z|≤(z-start)/2500000000)
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
      (w.cell.flow.valueErrorRadius w.start:ℝ) := by
    rw [hvalue,hstart]
    exact ReferenceFlowCell.valueErrorRadius_of_global hz.2 (herror z hwhole)
  exact ReferencePositionCell.checked_linked_force hs hm hk c w hc hl
    (w.cell.flow.timeParameter_mem hg.1 hz) hE hT herr

end OptimalG.Certificates.Transport
