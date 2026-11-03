import OptimalG.Certificates.ReferenceRefinedWeights
import OptimalG.Certificates.ReferenceWeightPositivity

/-! Positive interval bounds on a finite refined cover prove positivity of
the genuine reference ODE solution on the entire closed time interval. -/
namespace OptimalG.Certificates.Transport
open Set

theorem referenceFlowCoverCheck_closed_cover {start finish : ℚ}
    {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true) (ho : start<finish)
    {z : ℝ} (hz : z∈Icc (start:ℝ) finish) :
    ∃ c∈cells,z∈Icc (c.segment.left.z:ℝ) c.segment.right.z := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    exact False.elim (ho.ne he)
  | cons c cs ih =>
    obtain ⟨hh,ht⟩ := Bool.and_eq_true_iff.mp hc
    have hg : c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z := of_decide_eq_true hh
    by_cases he : z≤(c.segment.right.z:ℝ)
    · exact ⟨c,List.mem_cons_self,by simpa only [hg.1,mem_Icc] using And.intro hz.1 he⟩
    · have hgt : (c.segment.right.z:ℝ)<z := lt_of_not_ge he
      have htail : c.segment.right.z<finish := by exact_mod_cast hgt.trans_le hz.2
      obtain ⟨d,hd,hdz⟩ := ih ht htail ⟨hgt.le,hz.2⟩
      exact ⟨d,List.mem_cons_of_mem c hd,hdz⟩

theorem checked_reference_positive {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish L S : ℚ} (coarse : List ReferenceFlowCell)
    (horder : start<finish) (hcoarse : referenceFlowCoverCheck start finish coarse=true)
    (hcurve : trajectoryCheck L S (coarse.map ReferenceFlowCell.canonicalPiece)=true)
    (hpoly : coarse.all ReferenceFlowCell.canonicalPieceCheck=true)
    (cs : List ReferenceWeightCertificate)
    (hchecks : cs.all (fun c=>c.check s k)=true)
    (hpositive : cs.all (fun c=>c.cell.positivityCheck)=true)
    (hstart : cs.all (fun c=>decide (c.start=start))=true)
    (hcover : referenceFlowCoverCheck start finish (cs.map (fun c=>c.cell.flow))=true)
    (hrefined : ∀ c∈cs,∃ parent∈coarse,∃ lo hi : ℚ,
      parent.refinementCheck c.cell.flow lo hi=true)
    {Z : ℝ→ℝ}
    (herror : ∀ z∈Icc (start:ℝ) finish,
      |Z z-cubicPrimitive L S (coarse.map ReferenceFlowCell.canonicalPiece) z|≤
        (z-start)/2500000000) :
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
      (c.cell.flow.valueErrorRadius c.start:ℝ) := by
    rw [hvalue,of_decide_eq_true (List.all_eq_true.mp hstart c hc)]
    exact ReferenceFlowCell.valueErrorRadius_of_global hzflow.2 (herror z hz)
  have hn := List.all_eq_true.mp hchecks c hc
  have hn' := hn
  simp only [ReferenceWeightCertificate.check,Bool.and_eq_true] at hn'
  have hv := c.cell.flow.actualValueCheck_sound hs hk c.start c.cell.deficit hn'.1.2
    (c.cell.flow.timeParameter_mem hgeo.1 hzflow) he
  have hpos := List.all_eq_true.mp hpositive c hc
  have hlo : 0<c.cell.deficit.lo ∧ 0<c.cell.terminal.lo :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hpos).1
  exact IntegerInterval.positive hs hv hlo.1

end OptimalG.Certificates.Transport
