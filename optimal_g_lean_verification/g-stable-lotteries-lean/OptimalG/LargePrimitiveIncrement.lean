import OptimalG.LargeMassFlatEnvelope
import OptimalG.Certificates.SmallMassExpressions

/-! A restricted concave-increment bound for the large-mass primitive upper
envelope. The whole needed range lies before .313, so a cap tangent at the
head join covers the only change of formula. -/
namespace OptimalG
open Set Variational

/-- The cap lies below each tangent while its denominator is positive. -/
theorem cap_le_tangent {lam S x r : ℝ} (hprod : 0≤lam*S) (hx : x<1) (hr : r<1) :
    cap lam S r≤cap lam S x+capScore lam S x*(r-x) := by
  have hx0 : 1-x≠0 := (sub_pos.mpr hx).ne'
  have hr0 : 1-r≠0 := (sub_pos.mpr hr).ne'
  have he : cap lam S r-(cap lam S x+capScore lam S x*(r-x))=
      -(lam*S*(r-x)^2/((1-r)*(1-x)^2)) := by
    unfold cap capScore
    field_simp [hx0,hr0]
    ring
  have hd : 0≤lam*S*(r-x)^2/((1-r)*(1-x)^2) :=
    div_nonneg (mul_nonneg hprod (sq_nonneg _)) (by positivity)
  linarith only [he,hd]

/-- For two head ranks, their sum of primitives dominates the tangent at a
join between their maximum and their sum. -/
theorem head_sum_ge_join_tangent {F slope x d q : ℝ} (hs : slope≤0)
    (hd : d∈Icc (0:ℝ) x) (hq : q∈Icc (0:ℝ) x) (hjoin : x≤d+q) :
    F*x+slope*x^2/2+(F+slope*x)*(d+q-x)≤
      (F*d+slope*d^2/2)+(F*q+slope*q^2/2) := by
  have ht : 0≤d+q-x := sub_nonneg.mpr hjoin
  have hsq : (d+q-x)^2≤d*q := by
    have hh := mul_le_mul (show d+q-x≤d by linarith only [hq.2])
      (show d+q-x≤q by linarith only [hd.2]) ht hd.1
    simpa only [pow_two] using hh
  have hnonneg : 0≤d*q-(d+q-x)^2/2 := by nlinarith only [hsq,sq_nonneg (d+q-x)]
  have hm := mul_nonneg (neg_nonneg.mpr hs) hnonneg
  nlinarith only [hm]

/-- No new numerical certificate is needed for the sign of the affine head
slope on the established parameter rectangle. -/
theorem smallMass_head_slope_nonpos {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) :
    Certificates.SmallMassExpressions.slope lam S≤0 := by
  have hLS := mul_le_mul hL.2 hS.2 (by linarith only [hS.1] : 0≤S)
    (by norm_num : (0:ℝ)≤56233/100000)
  have hsq : (22493/40000:ℝ)^2≤lam^2 := pow_le_pow_left₀ (by norm_num) hL.1 2
  unfold Certificates.SmallMassExpressions.slope headSlope headInitial cap capScore
  norm_num
  nlinarith only [hL.1,hL.2,hLS,hsq]

/-- The restricted large-mass shift increment needed to prove the packing
term negative. Both low endpoints lie in the head; their sum may enter the
cap, and that case follows from its tangent. -/
theorem largePrimitiveUpper_small_increment {lam S d q : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hd : d∈Icc (0:ℝ) (9/40)) (hq : q∈Icc (0:ℝ) (7/100)) :
    largePrimitiveUpper lam S (Certificates.SmallMassExpressions.initial lam S)
      (Certificates.SmallMassExpressions.slope lam S) (d+q)-
      Certificates.SmallMassExpressions.primitive lam S q≤
        Certificates.SmallMassExpressions.primitive lam S d := by
  have hs := smallMass_head_slope_nonpos hL hS
  by_cases hh : d+q≤527/2000
  · rw [largePrimitiveUpper,largeRemainingUpper,if_pos hh]
    have hm := mul_nonpos_of_nonpos_of_nonneg hs (mul_nonneg hd.1 hq.1)
    unfold Certificates.SmallMassExpressions.primitive
    nlinarith only [hm]
  · have hcut : d+q≤313/1000 := by linarith only [hd.2,hq.2]
    have he : largePrimitiveUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) (d+q)=cap lam S (d+q) := by
      rw [largePrimitiveUpper,largeRemainingUpper,if_neg hh,if_pos hcut]
      unfold capDeficit
      ring
    rw [he]
    have ht := cap_le_tangent (lam:=lam) (S:=S) (x:=527/2000) (r:=d+q)
      (mul_nonneg (by linarith only [hL.1]) (by linarith only [hS.1]))
      (by norm_num) (by linarith only [hcut] : d+q<1)
    have hj := headPrimitive_at_join (527/2000) (cap lam S (527/2000))
      (capScore lam S (527/2000)) (by norm_num)
    have hf := headScore_at_join (527/2000) (cap lam S (527/2000))
      (capScore lam S (527/2000)) (by norm_num)
    have hb := head_sum_ge_join_tangent
      (F:=Certificates.SmallMassExpressions.initial lam S) hs
      (show d∈Icc (0:ℝ) (527/2000) from ⟨hd.1,by linarith only [hd.2]⟩)
      (show q∈Icc (0:ℝ) (527/2000) from ⟨hq.1,by linarith only [hq.2]⟩)
      (le_of_not_ge hh)
    change Certificates.SmallMassExpressions.initial lam S*(527/2000)+
      Certificates.SmallMassExpressions.slope lam S*(527/2000)^2/2=cap lam S (527/2000) at hj
    change Certificates.SmallMassExpressions.initial lam S+
      Certificates.SmallMassExpressions.slope lam S*(527/2000)=capScore lam S (527/2000) at hf
    rw [hj,hf] at hb
    unfold Certificates.SmallMassExpressions.primitive
    linarith only [ht,hb]

end OptimalG
