import OptimalG.Certificates.SmallMassExpressions

/-! Elementary positivity of every denominator used by the C.4 rational
certificates, on their full parameter range. No generated signs are needed. -/
namespace OptimalG.Certificates.SmallMassExpressions
open Set

theorem initial_formula (lam S : ℝ) :
    initial lam S=lam*(17357832000*lam-19352000000*S-7535468817)/2286894366 := by
  norm_num [initial,headInitial,Variational.cap,Variational.capScore]
  <;> ring

theorem slope_formula (lam S : ℝ) :
    slope lam S= -4000000*lam*(4339458*lam-3784000*S-2169729)/602596665441 := by
  norm_num [slope,headSlope,headInitial,Variational.cap,Variational.capScore]
  <;> ring

theorem initial_bounds {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    initial lam S∈Icc (43/100:ℝ) (443/1000) := by
  have hlam : 0≤lam := by linarith only [hL.1]
  have ha : 1760000000≤17357832000*lam-19352000000*S-7535468817 := by
    linarith only [hL.1,hS.2]
  have hb : 17357832000*lam-19352000000*S-7535468817≤1790000000 := by
    linarith only [hL.2,hS.1]
  have hlo := mul_le_mul hL.1 ha (by norm_num : (0:ℝ)≤1760000000) hlam
  have hhi := mul_le_mul hL.2 hb (by linarith only [ha] :
    0≤17357832000*lam-19352000000*S-7535468817) (by norm_num : (0:ℝ)≤56233/100000)
  rw [initial_formula]
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<2286894366)).mpr
    nlinarith only [hlo]
  · apply (div_le_iff₀ (by norm_num : (0:ℝ)<2286894366)).mpr
    nlinarith only [hhi]

theorem slope_bounds {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    slope lam S∈Icc (-1:ℝ) 0 := by
  have hlam : 0≤lam := by linarith only [hL.1]
  have ha : 0≤4339458*lam-3784000*S-2169729 := by
    linarith only [hL.1,hS.2]
  have hb : 4339458*lam-3784000*S-2169729≤200000 := by
    linarith only [hL.2,hS.1]
  have hp := mul_nonneg hlam ha
  have hhi := mul_le_mul hL.2 hb ha (by norm_num : (0:ℝ)≤56233/100000)
  rw [slope_formula]
  constructor
  · apply (le_div_iff₀ (by norm_num : (0:ℝ)<602596665441)).mpr
    nlinarith only [hhi]
  · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hp]) (by norm_num)

theorem cap28_pos {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    0<cap28 lam S := by
  have hl : 0<lam := by linarith only [hL.1]
  have hs : 0<162-625*S := by linarith only [hS.2]
  have he : cap28 lam S=lam*(162-625*S)/324 := by
    norm_num [cap28,Variational.capScore]
    <;> ring
  rw [he]
  exact div_pos (mul_pos hl hs) (by norm_num)

theorem cap2918_pos {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    0<cap2918 lam S := by
  have hl : 0<lam := by linarith only [hL.1]
  have hs : 0<12538681-50000000*S := by linarith only [hS.2]
  have he : cap2918 lam S=lam*(12538681-50000000*S)/25077362 := by
    norm_num [cap2918,Variational.capScore]
    <;> ring
  rw [he]
  exact div_pos (mul_pos hl hs) (by norm_num)

theorem denominator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (1/25:ℝ) (527/2000)) :
    0<denominator lam S p := by
  have hF := initial_bounds hL hS
  have hs := slope_bounds hL hS
  have hp0 : 0<p := by linarith only [hp.1]
  have hsp := mul_nonneg (by linarith only [hs.1] : 0≤slope lam S+1) hp0.le
  have hi : 0 < initial lam S+slope lam S*p/2 := by
    nlinarith only [hsp,hF.1,hp.2]
  have hR : 0<primitive lam S p := by
    have he : primitive lam S p=p*(initial lam S+slope lam S*p/2) := by
      unfold primitive
      ring
    rw [he]
    exact mul_pos hp0 hi
  have ht : (1473/2000:ℝ)≤1-p := by linarith only [hp.2]
  have hv : (3293/40000:ℝ)≤lam-(1-p)/2 := by linarith only [hL.1,hp.1]
  have hm := mul_le_mul ht hv (by norm_num : (0:ℝ)≤3293/40000)
    (by linarith only [hp.2] : 0≤1-p)
  have hP : 0<Variational.quadratic lam (1-p)-S := by
    unfold Variational.quadratic
    nlinarith only [hm,hS.2]
  unfold denominator smallMassDenominator
  linarith only [hR,hP]

end OptimalG.Certificates.SmallMassExpressions
