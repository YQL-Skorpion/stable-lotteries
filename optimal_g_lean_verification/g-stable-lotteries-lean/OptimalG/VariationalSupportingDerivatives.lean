import OptimalG.VariationalRegularPositive

/-! Genuine Fermat equations for active supporting lines, after the measurable
score has been recovered as a Lipschitz representative. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem derivative_eq_of_support_line {a b r theta v : ℝ} {f : ℝ → ℝ}
    (hr : r ∈ Ioo a b) (hd : HasDerivAt f v r)
    (hs : ∀ s ∈ Icc a b, f s+theta*s ≤ f r+theta*r) : v = -theta := by
  have hm : IsMaxOn (fun s => f s+theta*s) (Icc a b) r := by
    intro s hs'
    exact hs s hs'
  have hh := (hm.isLocalMax (Icc_mem_nhds hr.1 hr.2)).hasDerivAt_eq_zero
    (hd.add ((hasDerivAt_id r).const_mul theta))
  norm_num at hh
  linarith

theorem derivative_eq_line_at_saturation {a b r lam v : ℝ} {f : ℝ → ℝ}
    (hr : r ∈ Ioo a b) (hd : HasDerivAt f v r)
    (hceil : ∀ s ∈ Icc a b, f s ≤ lam-s) (heq : f r = lam-r) : v = -1 := by
  apply derivative_eq_of_support_line hr hd (theta:=1)
  intro s hs
  have hh := hceil s hs
  rw [heq]
  linarith

theorem active_x_derivative {lam z u a b r slope : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hgraph : ∀ s ∈ Icc a b, (s,psi s) ∈ rankScoreSupport d.phi)
    (hr : r ∈ Ioo a b) (hder : HasDerivAt psi slope r)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    (hx : v.1.2.1 = r) (hA : v.2.1 = psi r) : slope = -featureTheta lam d v := by
  apply derivative_eq_of_support_line hr hder
  intro s hs
  have hh := active_feature_supports_x hd hz huLow huHigh hv hactive (hgraph s hs)
  simpa only [hx,hA] using hh

theorem active_y_interior_derivative {lam z u a b r slope : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hgraph : ∀ s ∈ Icc a b, (s,psi s) ∈ rankScoreSupport d.phi)
    (hr : r ∈ Ioo a b) (hder : HasDerivAt psi slope r)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    (hy : v.1.2.2 = r) (hB : v.2.2 = psi r) (hpr : v.1.1 < r) :
    slope = -featureTheta lam d v := by
  apply derivative_eq_of_support_line (a:=max a v.1.1) ⟨max_lt hr.1 hpr,hr.2⟩ hder
  intro s hs
  have hs' : s ∈ Icc a b := ⟨(le_max_left _ _).trans hs.1,hs.2⟩
  have hp : v.1.1 ≤ s := (le_max_right _ _).trans hs.1
  have hh := active_feature_supports_y hd hz huLow huHigh hv hactive (hgraph s hs') hp
  simpa only [hy,hB] using hh

theorem active_y_boundary_with_right_x_derivative {lam z u a b r slope : ℝ}
    {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hgraph : ∀ s ∈ Icc a b, (s,psi s) ∈ rankScoreSupport d.phi)
    (hr : r ∈ Ioo a b) (hder : HasDerivAt psi slope r)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    (hy : v.1.2.2 = r) (hB : v.2.2 = psi r) (hp : v.1.1 = r) (hx : r ≤ v.1.2.1) :
    slope = -featureTheta lam d v := by
  have hxG := (hd.featureSupport_rankScores hv).1
  have hpx : v.1.1 ≤ v.1.2.1 := by rwa [hp]
  have hxy := active_feature_supports_y hd hz huLow huHigh hv hactive hxG hpx
  apply derivative_eq_of_support_line hr hder
  intro s hs
  have hh := active_feature_supports_x hd hz huLow huHigh hv hactive (hgraph s hs)
  have hsupport := hh.trans hxy
  simpa only [hy,hB] using hsupport

end OptimalG.Variational
