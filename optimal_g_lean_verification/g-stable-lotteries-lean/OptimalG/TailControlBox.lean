import OptimalG.TailControl

/-! A uniform tail-control derivative bound from coarse coupled-contact
coefficient boxes. Only four rational corners are needed: the expression
is affine in alpha and concave in the backward rank coordinate. -/
namespace OptimalG
open Set

 theorem tailControlSlope_nonneg_box {v kappa lam p theta alpha r : ℝ}
    (hv : (309/50:ℝ)≤v) (hk : kappa≤1273/100)
    (hL : lam≤56233/100000) (hp : p≤19/50)
    (htheta : theta≤81/100) (halpha : alpha∈Icc (0:ℝ) 3)
    (hr : r∈Icc (849/1000:ℝ) 1) :
    0≤tailControlSlope v kappa lam p theta alpha r := by
  have hd0 : 0≤1-r := sub_nonneg.mpr hr.2
  have hd1 : 1-r≤151/1000 := by linarith only [hr.1]
  have hvGain := mul_nonneg (sub_nonneg.mpr hv)
    (add_nonneg zero_le_one (mul_nonneg halpha.1 hd0))
  have hkGain := mul_nonneg (sub_nonneg.mpr hk)
    (add_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hd0)
      (mul_nonneg halpha.1 (sq_nonneg (1-r))))
  have hparam : 0≤alpha*((94233/100000)-(p+lam)) :=
    mul_nonneg halpha.1 (by linarith only [hL,hp])
  have hfloor := quadratic_nonneg_between
    ((309/50:ℝ)-81/100-alpha*(94233/100000))
    (alpha*(259/50)-1273/50) (-alpha*(1273/100)) 0 (151/1000)
    (by nlinarith only [halpha.1])
    (by norm_num; linarith only [halpha.2])
    (by norm_num; linarith only [halpha.2])
    (1-r) ⟨hd0,hd1⟩
  unfold tailControlSlope
  nlinarith only [hfloor,hvGain,hkGain,hparam,htheta]

/-- The coarse box proves both endpoint tests required by actual quadratic
completion, uniformly through the entire retained tail. -/
 theorem tailControlSlope_endpoints_box {z Y H lam p theta alpha : ℝ}
    (hz : z∈Ico (849/1000:ℝ) 1)
    (hv : (309/50:ℝ)≤tailBackwardSlope z Y H)
    (hk : tailBackwardCurvature z Y H≤1273/100)
    (hL : lam≤56233/100000) (hp : p≤19/50)
    (htheta : theta≤81/100) (halpha : alpha∈Icc (0:ℝ) 3) :
    0≤tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H)
      lam p theta alpha z ∧
    0≤tailControlSlope (tailBackwardSlope z Y H) (tailBackwardCurvature z Y H)
      lam p theta alpha 1 :=
  ⟨tailControlSlope_nonneg_box hv hk hL hp htheta halpha ⟨hz.1,hz.2.le⟩,
    tailControlSlope_nonneg_box hv hk hL hp htheta halpha (by norm_num)⟩

end OptimalG
