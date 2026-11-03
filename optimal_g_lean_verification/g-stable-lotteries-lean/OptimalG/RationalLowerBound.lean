import OptimalG.NecessaryFeasible
import OptimalG.MetricWitness
import OptimalG.OptimalityAssembly

/-! A fixed rational lower bound needs neither an attained variational
minimum nor an upper reference. Its finite witnesses follow directly from
necessary conditions, the universal LP bounds, and endpoint exclusion. -/
namespace OptimalG
open Set Variational

 theorem witness_212465_of_endpoint_exclusion
    (hLP : ∀ phi : ℝ→ℝ,NormalizedNecessaryConditions (22493/40000) phi →
      UniversalLPPrimitiveBounds phi)
    (hexclude : ¬Feasible (22493/40000))
    (g : ℝ→ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    WitnessAbove g (42493/20000) := by
  apply (witnessAbove_iff_not_universalBound g _).mpr
  intro hb
  have hb' : UniversalBound g (1+2*(22493/40000:ℝ)) := by
    convert hb using 1 <;> norm_num
  obtain ⟨phi,c,hc,hrelation,hn⟩ :=
    exists_normalized_necessary_conditions g hg (22493/40000)
      (by norm_num) (by norm_num) hb'
  exact hexclude (hn.variational_feasible
    (by constructor <;> norm_num) (hLP phi hn))

 theorem maximumDistortion_ge_212465_of_endpoint_exclusion
    (hLP : ∀ phi : ℝ→ℝ,NormalizedNecessaryConditions (22493/40000) phi →
      UniversalLPPrimitiveBounds phi)
    (hexclude : ¬Feasible (22493/40000))
    (g : ℝ→ℝ) (hg : AdmissibleActivation g) :
    ENNReal.ofReal (42493/20000:ℝ)≤maximumDistortion g :=
  witnessAbove_le_maximumDistortion g _
    (witness_212465_of_endpoint_exclusion hLP hexclude g hg.1)

end OptimalG
