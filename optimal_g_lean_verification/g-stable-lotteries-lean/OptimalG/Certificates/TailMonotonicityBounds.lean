import OptimalG.Certificates.TailMonotonicityData.Corner0
import OptimalG.Certificates.TailMonotonicityData.Corner1
import OptimalG.Certificates.TailMonotonicityData.Corner2
import OptimalG.Certificates.TailMonotonicityData.Corner3
import OptimalG.PolynomialCompletion

namespace OptimalG.Certificates.TailMonotonicity
open Set
set_option maxHeartbeats 0

noncomputable def primitiveCap (p : ℝ) : ℝ := (56233/100000)*p-p^2/2-227179/10000000
noncomputable def numerator (p Y H z : ℝ) : ℝ :=
  primitiveCap p*(1+tailSlope (539/625) Y H z)+
    p*(p-z-tailScore (539/625) Y H z)

private theorem affine_between_nonneg {f : ℝ→ℝ} {a b x : ℝ}
    (hab : a<b) (hx : x∈Icc a b) (ha : 0≤f a) (hb : 0≤f b)
    (he : (b-a)*f x=(b-x)*f a+(x-a)*f b) : 0≤f x := by
  have hl := mul_nonneg (sub_nonneg.mpr hx.2) ha
  have hr := mul_nonneg (sub_nonneg.mpr hx.1) hb
  have hh : 0≤(b-a)*f x := by rw [he];exact add_nonneg hl hr
  exact nonneg_of_mul_nonneg_right hh (sub_pos.mpr hab)

theorem corner0_positive {p z : ℝ} (hp : p∈Icc (41/50:ℝ) (37/40))
    (hz : z∈Icc (7/8:ℝ) 1) : 0<numerator p (8793/100000) (-3589/10000) z := by
  have hx : ∀ j,(TailMonotonicityData.Corner0.box j).Contains (![p,1-z,0] j) := by
    intro j
    fin_cases j
    · simpa [TailMonotonicityData.Corner0.box,RatInterval.Contains] using hp
    · norm_num [TailMonotonicityData.Corner0.box,RatInterval.Contains]
      constructor <;> linarith only [hz.1,hz.2]
    · norm_num [TailMonotonicityData.Corner0.box,RatInterval.Contains]
  have hh := TailMonotonicityData.Corner0.positive ![p,1-z,0] hx
  have he : TailMonotonicityData.Corner0.value p (1-z) 0=numerator p (8793/100000) (-3589/10000) z := by
    norm_num [TailMonotonicityData.Corner0.value,numerator,primitiveCap,
      tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    <;> ring
  exact he ▸ hh

theorem corner1_positive {p z : ℝ} (hp : p∈Icc (41/50:ℝ) (37/40))
    (hz : z∈Icc (7/8:ℝ) 1) : 0<numerator p (8793/100000) (-1757/5000) z := by
  have hx : ∀ j,(TailMonotonicityData.Corner1.box j).Contains (![p,1-z,0] j) := by
    intro j
    fin_cases j
    · simpa [TailMonotonicityData.Corner1.box,RatInterval.Contains] using hp
    · norm_num [TailMonotonicityData.Corner1.box,RatInterval.Contains]
      constructor <;> linarith only [hz.1,hz.2]
    · norm_num [TailMonotonicityData.Corner1.box,RatInterval.Contains]
  have hh := TailMonotonicityData.Corner1.positive ![p,1-z,0] hx
  have he : TailMonotonicityData.Corner1.value p (1-z) 0=numerator p (8793/100000) (-1757/5000) z := by
    norm_num [TailMonotonicityData.Corner1.value,numerator,primitiveCap,
      tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    <;> ring
  exact he ▸ hh

theorem corner2_positive {p z : ℝ} (hp : p∈Icc (41/50:ℝ) (37/40))
    (hz : z∈Icc (7/8:ℝ) 1) : 0<numerator p (221/2500) (-3589/10000) z := by
  have hx : ∀ j,(TailMonotonicityData.Corner2.box j).Contains (![p,1-z,0] j) := by
    intro j
    fin_cases j
    · simpa [TailMonotonicityData.Corner2.box,RatInterval.Contains] using hp
    · norm_num [TailMonotonicityData.Corner2.box,RatInterval.Contains]
      constructor <;> linarith only [hz.1,hz.2]
    · norm_num [TailMonotonicityData.Corner2.box,RatInterval.Contains]
  have hh := TailMonotonicityData.Corner2.positive ![p,1-z,0] hx
  have he : TailMonotonicityData.Corner2.value p (1-z) 0=numerator p (221/2500) (-3589/10000) z := by
    norm_num [TailMonotonicityData.Corner2.value,numerator,primitiveCap,
      tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    <;> ring
  exact he ▸ hh

theorem corner3_positive {p z : ℝ} (hp : p∈Icc (41/50:ℝ) (37/40))
    (hz : z∈Icc (7/8:ℝ) 1) : 0<numerator p (221/2500) (-1757/5000) z := by
  have hx : ∀ j,(TailMonotonicityData.Corner3.box j).Contains (![p,1-z,0] j) := by
    intro j
    fin_cases j
    · simpa [TailMonotonicityData.Corner3.box,RatInterval.Contains] using hp
    · norm_num [TailMonotonicityData.Corner3.box,RatInterval.Contains]
      constructor <;> linarith only [hz.1,hz.2]
    · norm_num [TailMonotonicityData.Corner3.box,RatInterval.Contains]
  have hh := TailMonotonicityData.Corner3.positive ![p,1-z,0] hx
  have he : TailMonotonicityData.Corner3.value p (1-z) 0=numerator p (221/2500) (-1757/5000) z := by
    norm_num [TailMonotonicityData.Corner3.value,numerator,primitiveCap,
      tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    <;> ring
  exact he ▸ hh

theorem numerator_nonneg {p Y H z : ℝ} (hp : p∈Icc (41/50:ℝ) (37/40))
    (hY : Y∈Icc (8793/100000:ℝ) (221/2500))
    (hH : H∈Icc (-3589/10000:ℝ) (-1757/5000))
    (hz : z∈Icc (7/8:ℝ) 1) : 0≤numerator p Y H z := by
  have h0 := (corner0_positive hp hz).le
  have h1 := (corner1_positive hp hz).le
  have h2 := (corner2_positive hp hz).le
  have h3 := (corner3_positive hp hz).le
  have hl : 0≤numerator p (8793/100000) H z := by
    apply affine_between_nonneg (by norm_num : (-3589/10000:ℝ)< -1757/5000) hH h0 h1
    simp only [numerator,tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    ring
  have hr : 0≤numerator p (221/2500) H z := by
    apply affine_between_nonneg (by norm_num : (-3589/10000:ℝ)< -1757/5000) hH h2 h3
    simp only [numerator,tailScore,tailSlope,tailOne,tailTwo,tailCoord]
    ring
  apply affine_between_nonneg (by norm_num : (8793/100000:ℝ)<221/2500) hY hl hr
  simp only [numerator,tailScore,tailSlope,tailOne,tailTwo,tailCoord]
  ring

end OptimalG.Certificates.TailMonotonicity
