import OptimalG.VariationalDiagonalDerivative
import OptimalG.VariationalSupportingDerivatives

/-! Fermat's equation along the actual coupled boundary y=p. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem active_y_diagonal_derivative {lam z u a b r slope : ℝ}
    {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hgraph : ∀ s ∈ Icc a b, (s,psi s) ∈ rankScoreSupport d.phi)
    (hr : r ∈ Ioo a b) (hpr : r ∈ Ioo pLo pHi)
    (hder : HasDerivAt psi slope r) (hJ : HasDerivAt (primitive lam d) (psi r) r)
    {v : ControlFeature} (hv : v ∈ controlFeatureSupport d)
    (hactive : featureH hd z u v = vectorField lam d z u)
    (hy : v.1.2.2 = r) (hB : v.2.2 = psi r) (hp : v.1.1 = r) :
    slope = Certificates.Control.diagonalSlope (z-lam) (2*lam-v.1.2.1) (2*r-lam)
      (primitive lam d r) (quadratic lam (1-r)-d.S) (quadratic lam (z-r)-d.S-u)
      v.2.1 (psi r) (1-r-lam) (z-r-lam) := by
  let f := diagonalValue lam d.S z u v.1.2.1 v.2.1 (primitive lam d) psi
  let lo := max a pLo
  let hi := min b pHi
  have hrI : r ∈ Ioo lo hi := ⟨max_lt hr.1 hpr.1,lt_min hr.2 hpr.2⟩
  have hxG := (hd.featureSupport_rankScores hv).1
  have hfeature (s : ℝ) (hs : s ∈ Icc lo hi) :
      ((s,v.1.2.1,s),v.2.1,psi s) ∈ controlFeatureSupport d := by
    have hsfree : s ∈ Icc a b := ⟨(le_max_left _ _).trans hs.1,hs.2.trans (min_le_left _ _)⟩
    have hsmass : s ∈ Icc pLo pHi := ⟨(le_max_right _ _).trans hs.1,hs.2.trans (min_le_right _ _)⟩
    exact hd.feature_mem_support_of_rankScores hsmass hxG (hgraph s hsfree) le_rfl
  have hvalue (s : ℝ) (hs : s ∈ Icc lo hi) :
      f s = featureH hd z u ((s,v.1.2.1,s),v.2.1,psi s) := by
    rw [featureH_eq_value hd z u v.2.1 (psi s) (hd.controlFeatureSupport_subset (hfeature s hs)).1]
    simp only [f,diagonalValue,two_mul]
  have hfr : f r = vectorField lam d z u := by
    rw [hvalue r ⟨hrI.1.le,hrI.2.le⟩]
    have he : ((r,v.1.2.1,r),v.2.1,psi r) = v := by
      ext <;> simp_all
    rw [he]
    exact hactive
  have hmin : IsMinOn f (Icc lo hi) r := by
    intro s hs
    change f r ≤ f s
    rw [hfr,hvalue s hs]
    exact (min_le_right _ _).trans (hd.essInf_le_featureH z u (hfeature s hs))
  have hdom := (hd.controlFeatureSupport_subset hv).1
  have hD : 0 < Certificates.Control.det (2*lam-v.1.2.1) (2*r-lam)
      (primitive lam d r) (quadratic lam (1-r)-d.S) := by
    have hh := hd.determinant_positive hdom
    unfold controlDeterminant at hh
    rw [hp,hy] at hh
    unfold Certificates.Control.det
    nlinarith only [hh]
  have hC : 0 < Certificates.Control.cy (z-lam) (2*lam-v.1.2.1)
      (quadratic lam (1-r)-d.S) (quadratic lam (z-r)-d.S-u) := by
    have hh := (hd.control_coefficients_positive hdom hz huLow huHigh).2
    rw [hp] at hh
    linarith
  have hdiag := diagonalValue_hasDerivAt (lam:=lam) (S:=d.S) (z:=z) (u:=u)
    (x:=v.1.2.1) (A:=v.2.1) hJ hder hD.ne'
  have hzder := (hmin.isLocalMin (Icc_mem_nhds hrI.1 hrI.2)).hasDerivAt_eq_zero hdiag
  have hnum := (div_eq_zero_iff.mp hzder).resolve_right (pow_ne_zero 2 hD.ne')
  exact (Certificates.Control.diagonal_derivative_zero_iff _ _ _ _ _ _ _ _ _ _ _ hD.ne' hC.ne').mp hnum

end OptimalG.Variational
