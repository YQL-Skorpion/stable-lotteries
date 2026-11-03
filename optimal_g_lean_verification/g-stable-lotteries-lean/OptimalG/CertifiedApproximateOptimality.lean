import OptimalG.ApproximateOptimalityAssembly
import OptimalG.CertifiedRationalLowerBound
import OptimalG.CertifiedRationalUpperBound

/-! The rational 10^-5 bracket, stated for actual finite-election distortion.
Every numerical and analytic hypothesis is discharged by imported proofs. -/
namespace OptimalG
open Set Certificates

/-- The lower witness may use a genuine metric, with positive comparison cost. -/
theorem certified_metric_witness_above_212465 (g : ℝ→ℝ)
    (hg : AdmissibleActivation g) :
    ∃ (E : Election) (D : Lottery E.candidateCount),E.Stable g D ∧
      ∃ m : MetricSpace E.Point,E.Consistent m.toPseudoMetricSpace ∧
        ∃ a : E.Candidate,0<E.candidateCost m.toPseudoMetricSpace a ∧
          (42493/20000:ℝ)*E.candidateCost m.toPseudoMetricSpace a <
            E.lotteryCost m.toPseudoMetricSpace D := by
  obtain ⟨E,D,hs,d,hd,a,_,hstrict⟩ := certified_witness_above_212465 g hg.1
  obtain ⟨m,hm,hpos,hcost⟩ := E.exists_positive_metric_witness D d hd a _ hstrict
  exact ⟨E,D,hs,m,hm,a,hpos,hcost⟩

theorem certified_optimalDistortion_bounds :
    ENNReal.ofReal (42493/20000:ℝ)≤optimalDistortion ∧
      optimalDistortion≤ENNReal.ofReal (106233/50000:ℝ) :=
  assemble_approximate_optimality (by norm_num) certifiedActivation
    certifiedActivation_admissible certified_upper_212466
    certified_maximumDistortion_ge_212465

theorem certifiedActivation_distortion_bounds :
    ENNReal.ofReal (42493/20000:ℝ)≤maximumDistortion certifiedActivation ∧
      maximumDistortion certifiedActivation≤ENNReal.ofReal (106233/50000:ℝ) :=
  ⟨certified_maximumDistortion_ge_212465 certifiedActivation certifiedActivation_admissible,
    (maximumDistortion_le_iff certifiedActivation (106233/50000) (by norm_num)).mpr
      certified_upper_212466⟩

end OptimalG
