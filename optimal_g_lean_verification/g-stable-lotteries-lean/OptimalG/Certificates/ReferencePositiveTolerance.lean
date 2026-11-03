import OptimalG.Certificates.ReferencePositiveFlow
import OptimalG.Certificates.ReferenceWeightTolerance

/-! The genuine coarse reference stays positive using its explicit error
rate and the checked widened deficit boxes on the whole time cover. -/
namespace OptimalG.Certificates.Transport
open Set

theorem checked_reference_positive_with_error {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish L S : ℚ} (coarse : List ReferenceFlowCell)
    (horder : start<finish) (hcoarse : referenceFlowCoverCheck start finish coarse=true)
    (hcurve : trajectoryCheck L S (coarse.map ReferenceFlowCell.canonicalPiece)=true)
    (hpoly : coarse.all ReferenceFlowCell.canonicalPieceCheck=true)
    (cs : List ReferenceWeightCertificate) (error : ReferenceWeightCertificate→ℚ)
    (hchecks : cs.all (fun c=>c.checkWithError s k (error c))=true)
    (hpositive : cs.all (fun c=>c.cell.positivityCheck)=true)
    (hcover : referenceFlowCoverCheck start finish (cs.map (fun c=>c.cell.flow))=true)
    (hrefined : ∀ c∈cs,∃ parent∈coarse,∃ lo hi : ℚ,
      parent.refinementCheck c.cell.flow lo hi=true)
    {rate : ℝ} (hrate : 0≤rate)
    (hradius : ∀ c∈cs,rate*((c.cell.flow.segment.right.z:ℝ)-start)≤error c)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S (coarse.map ReferenceFlowCell.canonicalPiece) z|≤
        rate*(z-start)) :
    ∀ z∈Icc (start:ℝ) finish,0<Z z := by
  intro z hz
  obtain ⟨flow,hflow,hzflow⟩ := referenceFlowCoverCheck_closed_cover hcover horder hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hflow
  obtain ⟨parent,hp,lo,hi,hr⟩ := hrefined c hc
  have hbounds := referenceFlowCoverCheck_bounds hcoarse hp
  have hgeo := ReferenceFlowCell.refinement_time_geometry hr hbounds.2.1
  have hvalue := refined_polynomial_global hcoarse hp hr hcurve
    (List.mem_map.mpr ⟨parent,hp,rfl⟩) (List.all_eq_true.mp hpoly parent hp) hzflow
  have he : |Z z-c.cell.flow.valuePolynomial.eval (c.cell.flow.timeParameter z)|≤
      (error c:ℝ) := by
    rw [hvalue]
    exact (herror z hz).trans
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right hzflow.2 _) hrate).trans (hradius c hc))
  have hn := List.all_eq_true.mp hchecks c hc
  have hn' := hn
  simp only [ReferenceWeightCertificate.checkWithError,Bool.and_eq_true] at hn'
  have hv := c.cell.flow.actualValueCheckWithError_sound hs hk (error c) c.cell.deficit hn'.1.2
    (c.cell.flow.timeParameter_mem hgeo.1 hzflow) he
  have hpos := List.all_eq_true.mp hpositive c hc
  have hlo : 0<c.cell.deficit.lo ∧ 0<c.cell.terminal.lo :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hpos).1
  exact IntegerInterval.positive hs hv hlo.1


end OptimalG.Certificates.Transport
