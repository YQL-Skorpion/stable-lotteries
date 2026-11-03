import OptimalG.BinaryCurveGeometry

/-! Scalar envelope comparisons for a fixed central binary certificate. The
polynomial checks can select a different envelope on each rational box. -/
namespace OptimalG
open Set Variational

namespace BinaryCurveGeometry

theorem headCapError_nonpos {phi : ℝ → ℝ} {lam S slope c : ℝ}
    (g : BinaryCurveGeometry phi lam S slope c) (h : VerifierCurve phi lam)
    {r : ℝ} (hr : r ∈ Icc (0:ℝ) (53/100)) :
    binaryHeadCapError lam S (phi 0) slope (527/2000) c r ≤ 0 := by
  unfold binaryHeadCapError
  split_ifs with hh hm hc
  · have hu := g.cap_upper r hr
    rw [h.affine_head_primitive g.head ⟨hr.1,hh⟩] at hu
    linarith only [hu]
  · have hu := g.cap_upper r hr
    rw [g.line_primitive r ⟨by linarith only [hm],by linarith only [hr.2]⟩] at hu
    linarith only [hu]
  · exact min_le_left _ _
  · exact le_rfl

end BinaryCurveGeometry

theorem binaryHeadCapError_le_area {lam S phi0 slope xh c r E : ℝ}
    (hxc : xh<c) (hcr : c≤r) (hE : 0≤E)
    (harea : binaryCentralUpperArea lam S c r≤E) :
    binaryHeadCapError lam S phi0 slope xh c r ≤
      quadratic lam r-S+E-cap lam S r := by
  have hxr : ¬r≤xh := not_le.mpr (hxc.trans_le hcr)
  unfold binaryHeadCapError
  rw [if_neg hxr]
  split_ifs with hm
  · linarith only [hE]
  · exact (min_le_right _ _).trans (by linarith only [harea])

theorem cap_error_envelope_nonneg {lam S c r : ℝ}
    (hdisc : (capSlack lam S c)^2≤(309/500)*capDeficit lam S c) :
    0≤capDeficit lam S c-capSlack lam S c*(r-c)+(309/2000)*(r-c)^2 := by
  have hh := sq_nonneg ((309/1000:ℝ)*(r-c)-capSlack lam S c)
  nlinarith only [hdisc,hh]

theorem binaryHeadCapError_le_cap_envelope {lam S phi0 slope xh c r : ℝ}
    (hxc : xh<c) (hcr : c≤r)
    (hdisc : (capSlack lam S c)^2≤(309/500)*capDeficit lam S c) :
    binaryHeadCapError lam S phi0 slope xh c r ≤
      quadratic lam r-S+capDeficit lam S c-capSlack lam S c*(r-c)+
        (309/2000)*(r-c)^2-cap lam S r := by
  have hh := binaryHeadCapError_le_area (phi0:=phi0) (slope:=slope) hxc hcr
    (cap_error_envelope_nonneg hdisc (r:=r))
    (min_le_right (binaryAreaUpper (309/1000) (348541/1000000)
      (87/1000000000) (24/100000) r) _)
  linarith only [hh]

theorem binaryHeadCapError_le_right_envelope {lam S phi0 slope xh c r : ℝ}
    (hxc : xh<c) (hcr : c≤r) (hr : (348541/1000000:ℝ)≤r) :
    binaryHeadCapError lam S phi0 slope xh c r ≤
      quadratic lam r-S+87/1000000000-cap lam S r := by
  apply binaryHeadCapError_le_area hxc hcr (by norm_num)
  have hh := min_le_left (binaryAreaUpper (309/1000) (348541/1000000)
    (87/1000000000) (24/100000) r)
    (capDeficit lam S c-capSlack lam S c*(r-c)+(309/2000)*(r-c)^2)
  simpa only [binaryCentralUpperArea,binaryAreaUpper,
    max_eq_right (sub_nonpos.mpr hr),mul_zero,zero_pow (by decide : 2≠0),
    div_zero,add_zero] using hh

end OptimalG
