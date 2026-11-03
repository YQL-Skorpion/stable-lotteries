import OptimalG.Certificates.HighMassData.RatioZero
import OptimalG.Certificates.HighMassData.RatioMiddle
import OptimalG.Certificates.SmallMassDenominators
import OptimalG.HighMassGeometry

/-! The global low-rank ratio bound needs only two scalar head checks,
the already proved lower slope bound, and the straight middle segment. -/
namespace OptimalG.Certificates
open Set SmallMassExpressions

theorem highMass_ratio_zero {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    lam < (129/100)*initial lam S := by
  have hn := HighMassData.RatioZero.numerator_pos hL hS
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
  have he : HighMassData.RatioZero.numerator lam S 0=(129/100)*initial lam S-lam := by
    rw [initial_formula]
    norm_num [HighMassData.RatioZero.numerator]
    <;> ring
  rw [he] at hn
  linarith only [hn]

theorem highMass_ratio_middle {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    lam-9/25 < (129/100)*(Variational.capScore lam S (527/2000)+527/2000-9/25) := by
  have hn := HighMassData.RatioMiddle.numerator_pos hL hS
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
  have he : HighMassData.RatioMiddle.numerator lam S 0=
      (129/100)*(Variational.capScore lam S (527/2000)+527/2000-9/25)-(lam-9/25) := by
    norm_num [HighMassData.RatioMiddle.numerator,Variational.capScore]
    <;> ring
  rw [he] at hn
  linarith only [hn]

theorem highMass_low_ratio {phi : ℝ→ℝ} {lam S : ℝ}
    (h : VerifierCurve phi lam)
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=score lam S r)
    (hline : ∀ r∈Icc (9/25:ℝ) lam,phi r=lam-r)
    (hfall : ∀ a b,0≤a→a≤b→b≤9/25→a-b≤phi b-phi a) :
    ∀ x∈Ico (0:ℝ) lam,lowRankRatio phi lam x≤129/100 := by
  have hz := highMass_ratio_zero hL hS
  have hm := highMass_ratio_middle hL hS
  have hjoin : score lam S (527/2000)=Variational.capScore lam S (527/2000) :=
    headScore_at_join _ _ _ (by norm_num)
  have hxhead : phi (527/2000)=Variational.capScore lam S (527/2000) := by
    rw [hhead (527/2000) ⟨by norm_num,le_rfl⟩,hjoin]
  have hj : 0≤(129/100)*initial lam S-lam+
      (1+(129/100)*slope lam S)*(527/2000)+0*(527/2000)^2 := by
    have hs := hjoin
    unfold score at hs
    nlinarith only [hm,hs]
  have hfirst := quadratic_nonneg_between ((129/100)*initial lam S-lam)
    (1+(129/100)*slope lam S) 0 0 (527/2000) (by norm_num)
    (by nlinarith only [hz]) hj
  intro x hx
  unfold lowRankRatio
  apply (div_le_iff₀ (h.positive hx)).mpr
  by_cases hxh : x≤527/2000
  · have hh := hfirst x ⟨hx.1,hxh⟩
    rw [hhead x ⟨hx.1,hxh⟩]
    unfold score
    nlinarith only [hh]
  · by_cases hx36 : x≤9/25
    · have hh := hfall (527/2000) x (by norm_num) (le_of_not_ge hxh) hx36
      rw [hxhead] at hh
      nlinarith only [hh,hm,hx36]
    · rw [hline x ⟨le_of_not_ge hx36,hx.2.le⟩]
      linarith only [hx.2]

end OptimalG.Certificates
