import OptimalG.Certificates.ReferenceExponentCertificate
import OptimalG.Certificates.ReferenceRefinedWeights

/-! Checked refined alpha masses and checked suffix additions enclose the
actual adjoint exponent everywhere, for the same coarse field as the ODE. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem checked_reference_exponents {s k : ℕ} (hs : 0<s) (hk : 0<k)
    {start finish : ℚ} (coarse : List ReferenceFlowCell)
    (hcover : referenceFlowCoverCheck start finish coarse=true)
    (cs : List ReferenceExponentCertificate)
    (hweights : cs.all (fun c=>c.weight.check s k)=true)
    (hexponents : cs.all (fun c=>c.check s)=true)
    (hcumulative : cumulativeIntegralCheck s start finish (cs.map (·.interval))=true)
    (hrefined : ∀ c∈cs,∃ parent∈coarse,∃ lo hi : ℚ,
      parent.refinementCheck c.weight.cell.flow lo hi=true)
    (hintegrable : IntervalIntegrable (referenceField ReferenceFlowCell.actualAlpha coarse)
      volume (start:ℝ) finish) :
    ∀ c∈cs,∀ z∈Icc (c.interval.lo:ℝ) c.interval.hi,
      c.weight.cell.exponent.Contains s
        (∫ x in z..(finish:ℝ),referenceField ReferenceFlowCell.actualAlpha coarse x) := by
  let alpha := referenceField ReferenceFlowCell.actualAlpha coarse
  have hglobal : (start:ℝ)≤finish := by
    exact_mod_cast referenceFlowCoverCheck_order hcover
  have hcell (c : ReferenceExponentCertificate) (hc : c∈cs) :
      IntervalIntegrable alpha volume (c.interval.lo:ℝ) c.interval.hi ∧
      c.interval.mass.Contains s (∫ x in (c.interval.lo:ℝ)..c.interval.hi,alpha x) := by
    obtain ⟨parent,hp,lo,hi,hr⟩ := hrefined c hc
    have hb := referenceFlowCoverCheck_bounds hcover hp
    have hg := ReferenceFlowCell.refinement_time_geometry hr hb.2.1
    have hlo : (start:ℝ)≤c.interval.lo := by exact_mod_cast hb.1.trans hg.2.1
    have hhi : (c.interval.hi:ℝ)≤finish := by exact_mod_cast hg.2.2.1.trans hb.2.2
    have horder : (c.interval.lo:ℝ)≤c.interval.hi := by exact_mod_cast hg.1.le
    refine ⟨hintegrable.mono_set ?_,?_⟩
    · rw [uIcc_of_le horder,uIcc_of_le hglobal]
      exact Icc_subset_Icc hlo hhi
    · exact checked_refined_alpha_mass hs hk c.weight
        (List.all_eq_true.mp hweights c hc) hcover hp hr
  have hcumul := cumulativeIntegralCheck_sound hcumulative (fun cell hmem=>by
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hmem
    exact hcell c hc)
  intro c hc z hz
  obtain ⟨parent,hp,lo,hi,hr⟩ := hrefined c hc
  have hf := hcumul.2.2 c.interval (List.mem_map.mpr ⟨c,hc,rfl⟩)
  exact c.checked_exponent hs (List.all_eq_true.mp hexponents c hc) hz (hcell c hc).1 hf.1
    (checked_refined_alpha_bound hs hk c.weight (List.all_eq_true.mp hweights c hc) hcover hp hr) hf.2

end OptimalG.Certificates.Transport
