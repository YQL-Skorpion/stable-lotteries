import OptimalG.Certificates.StaticLowAdmissible
import OptimalG.VariationalRepresentativeGraph

/-! Exact identification of the static primitive and its pointwise graph
with the genuine low-rank variational definitions. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem primitive_staticLow (r : ℝ) :
    primitive Certificates.StaticLow.lam staticLowData r=Certificates.StaticLow.primitive r := by
  unfold primitive
  split_ifs with hre hrt
  · change Certificates.cap Certificates.StaticLow.lam Certificates.StaticLow.slack r=_
    exact (Certificates.StaticLow.primitive_cap (by
      have hh := Certificates.StaticLow.contacts_real.1
      norm_num [ell] at hre
      linarith only [hre,hh])).symm
  · exact lowPrimitive_staticLow r
  · change Certificates.quadratic Certificates.StaticLow.lam r-Certificates.StaticLow.slack=_
    exact (Certificates.StaticLow.primitive_line (by
      have hh := Certificates.StaticLow.contacts_real.2.2.2
      norm_num [tEnd] at hrt
      linarith only [hrt,hh])).symm

theorem staticLow_score_graph {r : ℝ} (hr : r∈Icc xLo xHi) :
    (r,Certificates.StaticLow.score r)∈rankScoreSupport staticLowData.phi :=
  staticLow_admissible.continuous_rep_score_mem (by norm_num [xLo,xHi]) le_rfl le_rfl
    Certificates.StaticLow.continuous_score (Filter.Eventually.of_forall (fun _ => rfl)) hr

end OptimalG.Variational
