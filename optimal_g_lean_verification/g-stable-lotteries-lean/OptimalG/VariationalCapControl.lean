import OptimalG.TailContact
import OptimalG.VariationalHighShape
import OptimalG.VariationalFeatureGeometry

/-! A fixed diagonal cap control bounds the original continuation. This
uses its essential score graph and is independent of any terminal completion. -/
namespace OptimalG.Variational
open Set

noncomputable def capDiagonalTheta (lam S p r : ℝ) : ℝ :=
  (cap lam S p+quadratic lam (1-p)-S)*capScore lam S r/
    ((2*lam-r)*cap lam S p-(p+r-lam)*(quadratic lam (1-p)-S))

noncomputable def capDiagonalAlpha (lam S p r : ℝ) : ℝ :=
  (p+lam)*capScore lam S r/
    ((2*lam-r)*cap lam S p-(p+r-lam)*(quadratic lam (1-p)-S))

theorem capDiagonal_coefficients {lam p r : ℝ} {d : LowRankData}
    (hR : primitive lam d p=cap lam d.S p) :
    featureTheta lam d ((p,r,r),capScore lam d.S r,capScore lam d.S r)=
      capDiagonalTheta lam d.S p r ∧
    featureAlpha lam d ((p,r,r),capScore lam d.S r,capScore lam d.S r)=
      capDiagonalAlpha lam d.S p r := by
  simp only [featureTheta,featureAlpha,controlDeterminant,
    Certificates.Control.det,Certificates.Control.theta,
    Certificates.Control.alphaNumerator,capDiagonalTheta,capDiagonalAlpha,hR]
  constructor <;> ring

theorem original_continuation_cap_control {lam p r : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (hp : p∈Icc pLo pHi)
    (hr : (r,capScore lam d.S r)∈rankScoreSupport d.phi) (hpr : p≤r)
    (hR : primitive lam d p=cap lam d.S p) :
    ∀ z∈Ioo zStart zEnd,
      HasDerivAt Y (vectorField lam d z (Y z)) z ∧
      vectorField lam d z (Y z)≤
        highAffineControl lam d.S p (capDiagonalTheta lam d.S p r)
          (capDiagonalAlpha lam d.S p r) Y z := by
  have hv := hd.feature_mem_support_of_rankScores hp hr hr hpr
  have hc := capDiagonal_coefficients (r:=r) hR
  intro z hz
  refine ⟨(hY.2 z ⟨hz.1.le,hz.2.le⟩).hasDerivAt (Icc_mem_nhds hz.1 hz.2),?_⟩
  have hh := (min_le_right (lam-z)
    (essInf (controlH lam d z (Y z)) controlMeasure)).trans
      (hd.essInf_le_featureH z (Y z) hv)
  change vectorField lam d z (Y z)≤_ at hh
  rw [featureH_as_highAffineControl hd hv Y z] at hh
  simpa only [hc.1,hc.2] using hh

theorem original_continuation_fixed_cap_control {lam : ℝ} {d : LowRankData} {Y : ℝ→ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (hr : ((1459/5000:ℝ),capScore lam d.S (1459/5000))∈rankScoreSupport d.phi)
    (hR : primitive lam d (29/100)=cap lam d.S (29/100)) :
    ∀ z∈Icc (807/1000:ℝ) (17/20),
      HasDerivAt Y (vectorField lam d z (Y z)) z ∧
      vectorField lam d z (Y z)≤
        highAffineControl lam d.S (29/100)
          (capDiagonalTheta lam d.S (29/100) (1459/5000))
          (capDiagonalAlpha lam d.S (29/100) (1459/5000)) Y z := by
  have hh := original_continuation_cap_control hd hY
    (show (29/100:ℝ)∈Icc pLo pHi by norm_num [pLo,pHi]) hr
    (by norm_num : (29/100:ℝ)≤1459/5000) hR
  intro z hz
  exact hh z ⟨by norm_num [zStart] at *; linarith only [hz.1],
    by norm_num [zEnd] at *; linarith only [hz.2]⟩

end OptimalG.Variational
