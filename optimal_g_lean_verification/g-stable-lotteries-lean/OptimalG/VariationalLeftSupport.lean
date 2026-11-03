import OptimalG.VariationalGeometryLipschitz
import OptimalG.VariationalRightSupport

/-! A uniform left Lipschitz bound at active second positions. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

private theorem quadratic_unit_range {lam r : ℝ} (hl : lam ∈ Icc (0:ℝ) 1) (hr : r ∈ Icc (0:ℝ) 1) :
    -1 ≤ quadratic lam r ∧ quadratic lam r ≤ 1 := by
  have hp0 := mul_nonneg hl.1 hr.1
  have hp1 := mul_le_mul hl.2 hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 1)
  have hr2 := mul_le_mul hr.2 hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 1)
  unfold quadratic
  constructor <;> nlinarith [sq_nonneg r]

theorem Admissible.root_state_coarse_range {lam z u : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u)
    (huHigh : u ≤ quadratic lam z-d.S) : u ∈ Icc (-10:ℝ) 10 := by
  have hl : lam ∈ Icc (0:ℝ) 1 := by
    have hh := hd.1
    norm_num [lambdaLo,lambdaHi] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hz' : z ∈ Icc (0:ℝ) 1 := by
    have hh := hz
    norm_num [zStart,zEnd] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hQz := quadratic_unit_range hl hz'
  have hQ1 := quadratic_unit_range hl (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
  have hS := hd.slack_lower
  constructor <;> linarith [hQz.1,hQz.2,hQ1.1,hQ1.2]

/-- Coupling p with the second rank preserves admissibility. The resulting
control comparison uniformly bounds all leftward score drops at an active
second position, including the boundary y=p. -/
theorem Admissible.exists_active_y_left_bound {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    ∃ L : ℝ≥0, ∀ z ∈ Icc zStart zEnd, ∀ u : ℝ,
      quadratic lam z-quadratic lam 1 ≤ u → u ≤ quadratic lam z-d.S →
      ∀ v ∈ controlFeatureSupport d, featureH hd z u v = vectorField lam d z u →
      ∀ w ∈ rankScoreSupport d.phi, w.1 ≤ v.1.2.2 →
        w.2-v.2.2 ≤ L*(v.1.2.2-w.1) := by
  obtain ⟨K,hK⟩ := hd.geometric_control_lipschitz
  refine ⟨250*K,?_⟩
  intro z hz u huLow huHigh v hv hactive w hw hsw
  have hc := (hd.controlFeatureSupport_subset hv).1
  have hwBounds := hd.rankScoreSupport_bounds hw
  let p' := min v.1.1 w.1
  let c' : Control := (p',v.1.2.1,w.1)
  have hp' : p' ∈ Icc pLo pHi := by
    constructor
    · apply le_min hc.1.1
      exact (by norm_num [pLo,xLo] : pLo ≤ xLo).trans hwBounds.1.1
    · exact (min_le_left _ _).trans hc.1.2
  have hc' : c' ∈ controlDomain := by
    refine ⟨hp',hc.2.1,?_⟩
    exact ⟨max_le hwBounds.1.1 (min_le_right _ _),hwBounds.1.2⟩
  have hv' := hd.feature_mem_support_of_rankScores hp' (hd.featureSupport_rankScores hv).1 hw (min_le_right _ _)
  have hnew : featureH hd z u v ≤ featureH hd z u (c',v.2.1,w.2) := by
    rw [hactive]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH z u hv')
  let C := Certificates.Control.cy (z-lam) (2*lam-v.1.2.1)
    (quadratic lam (1-p')-d.S) (quadratic lam (z-p')-d.S-u)
  let D := controlDeterminant lam d c'
  have hC : (0.024:ℝ) < C := (hd.control_coefficients_positive hc' hz huLow huHigh).2
  have hD : 0 < D := by have hh := hd.determinant_positive hc'; change (3:ℝ)/100 < D at hh; linarith
  have hDmax : D ≤ 3 := hd.determinant_le_three hc'
  have hratio : (1:ℝ)/125 ≤ C/D := by
    apply (le_div_iff₀ hD).mpr
    linarith
  have hchange : featureH hd z u (c',v.2.1,w.2)-featureH hd z u (c',v.2.1,v.2.2) =
      -(C/D)*(w.2-v.2.2) := by
    rw [featureH_eq_value hd z u v.2.1 w.2 hc',featureH_eq_value hd z u v.2.1 v.2.2 hc']
    simpa only [C,D,c',controlDeterminant,Certificates.Control.det,neg_div] using Certificates.Control.value_scoreB_difference (z-lam) (2*lam-v.1.2.1)
      (p'+w.1-lam) (primitive lam d p') (quadratic lam (1-p')-d.S)
      (quadratic lam (z-p')-d.S-u) v.2.1 v.2.2 w.2
  have hgeometric := hK z hz u (hd.root_state_coarse_range hz huLow huHigh)
    v.1.1 p' v.1.2.1 v.1.2.2 w.1 v.2.1 v.2.2 hc hc'
    (hd.controlFeatureSupport_subset hv).2.1 (hd.controlFeatureSupport_subset hv).2.2
  have hpyr : v.1.1 ≤ v.1.2.2 := (le_max_right _ _).trans hc.2.2.1
  have hpp : p' ≤ v.1.1 := min_le_left _ _
  have hdp : v.1.1-p' ≤ v.1.2.2-w.1 := by
    dsimp [p']
    by_cases hpw : v.1.1 ≤ w.1
    · rw [min_eq_left hpw]
      linarith
    · rw [min_eq_right (le_of_not_ge hpw)]
      linarith
  rw [abs_of_nonneg (sub_nonneg.mpr hpp),abs_of_nonneg (sub_nonneg.mpr hsw)] at hgeometric
  have hgeom : featureH hd z u (c',v.2.1,v.2.2)-featureH hd z u v ≤
      2*(K:ℝ)*(v.1.2.2-w.1) := by
    have hh := neg_abs_le (featureH hd z u v-featureH hd z u (c',v.2.1,v.2.2))
    have hm := mul_le_mul_of_nonneg_left hdp K.coe_nonneg
    change |featureH hd z u v-featureH hd z u (c',v.2.1,v.2.2)| ≤ _ at hgeometric
    nlinarith only [hh,hgeometric,hm]
  change w.2-v.2.2 ≤ (250:ℝ)*K*(v.1.2.2-w.1)
  by_cases hgap : 0 ≤ w.2-v.2.2
  · have hm := mul_le_mul_of_nonneg_right hratio hgap
    nlinarith only [hnew,hchange,hgeom,hm]
  · have hnonneg := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 250) K.coe_nonneg) (sub_nonneg.mpr hsw)
    exact (le_of_not_ge hgap).trans hnonneg

end OptimalG.Variational
