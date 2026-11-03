import OptimalG.VariationalBump
import OptimalG.VariationalFinitePerturbation

/-! Exact control improvement under an inactive score bump. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def bumpRatio (lam p : ℝ) : ℝ := lam/(1-min p ell)
noncomputable def bumpPrimitive (h : ℝ → ℝ) (p : ℝ) : ℝ :=
  if p ≤ ell then 0 else ∫ r in ell..p,h r

theorem primitive_bumpData {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {h : ℝ → ℝ} (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd))) (t : ℝ)
    {p : ℝ} (hp : p ∈ Icc pLo pHi) :
    primitive lam (bumpData lam d h t) p = primitive lam d p+
      bumpRatio lam p*bumpShift lam h t+t*bumpPrimitive h p := by
  have hpte : p ≤ tEnd := hp.2.trans (by norm_num [pHi, tEnd])
  by_cases hpe : p ≤ ell
  · simp only [primitive, hpe, if_pos, bumpData, cap_slack_decrease,
      bumpRatio, min_eq_left hpe, bumpPrimitive, mul_zero, add_zero]
    ring
  · simp only [primitive, hpe, if_neg, hpte, if_pos, bumpRatio,
      min_eq_right (lt_of_not_ge hpe).le, bumpPrimitive]
    rw [lowPrimitive_bumpData hd hh t ⟨(lt_of_not_ge hpe).le,hpte⟩]
    simp only [ite_false]
    ring

theorem bumpPrimitive_nonneg {h : ℝ → ℝ}
    (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd)))
    (h0 : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r)
    {p : ℝ} (hp : p ∈ Icc pLo pHi) : 0 ≤ bumpPrimitive h p := by
  unfold bumpPrimitive
  split_ifs with hpe
  · exact le_rfl
  · exact (bump_partial_bounds hh h0
      ⟨(lt_of_not_ge hpe).le,hp.2.trans (by norm_num [pHi,tEnd])⟩).1

theorem bumpRatio_gt {lam p : ℝ} (hl : lam ∈ Icc lambdaLo lambdaHi)
    (hp : p ∈ Icc pLo pHi) : (0.74 : ℝ) < bumpRatio lam p := by
  have hmin : pLo ≤ min p ell := le_min hp.1 (by norm_num [pLo,ell])
  have hmax : min p ell ≤ ell := min_le_right _ _
  have hden : 0 < 1-min p ell := by
    change min p ell ≤ (28 : ℝ)/100 at hmax
    linarith
  unfold bumpRatio
  apply (lt_div_iff₀ hden).mpr
  have hll := hl.1
  change (562325 : ℝ)/1000000 ≤ lam at hll
  change (1 : ℝ)/4 ≤ min p ell at hmin
  linarith

/-- Whenever both score coordinates avoid the bump, a sufficiently near-active
control improves under the exact compensating S/state shift. -/
theorem Admissible.bump_control_nondecreasing {lam t : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {h : ℝ → ℝ}
    (hh : MemLp h ⊤ (volume.restrict (Icc ell tEnd)))
    (h0 : ∀ᵐ r ∂volume.restrict (Icc ell tEnd), 0 ≤ h r) (ht : 0 ≤ t)
    (hdn : Admissible lam (bumpData lam d h t))
    {c : Control} (hc : c ∈ controlDomain) {z u : ℝ} (hz : z ∈ Icc zStart zEnd)
    (huLow : quadratic lam z-quadratic lam 1 ≤ u) (huHigh : u ≤ quadratic lam z-d.S)
    (hfx : d.phi c.2.1 ≤ lam-c.2.1) (hfy : d.phi c.2.2 ≤ lam-c.2.2)
    (hnear : controlH lam d z u c ≤ lam-z+1/10000)
    (hx : h c.2.1 = 0) (hy : h c.2.2 = 0) :
    controlH lam d z u c ≤ controlH lam (bumpData lam d h t) z (u+bumpShift lam h t) c := by
  let q := bumpShift lam h t
  let v := bumpRatio lam c.1
  let R := primitive lam d c.1
  let P := quadratic lam (1-c.1)-d.S
  let K := quadratic lam (z-c.1)-d.S-u
  let dR := v*q+t*bumpPrimitive h c.1
  have hmass : 0 ≤ bumpMass h :=
    (bump_partial_bounds hh h0 (by norm_num [ell,tEnd])).1
  have hq : 0 ≤ q := div_nonneg (mul_nonneg ht hmass) (bumpScalar_pos hd.1).le
  have hdR : v*q ≤ dR := by
    have hh0 := mul_nonneg ht (bumpPrimitive_nonneg hh h0 hc.1)
    dsimp [dR]
    linarith
  have hRn : primitive lam (bumpData lam d h t) c.1 = R+dR := by
    rw [primitive_bumpData hd hh t hc.1]
    dsimp [R,dR,v,q]
    ring
  have hPn : quadratic lam (1-c.1)-(bumpData lam d h t).S = P+q := by dsimp [bumpData,P,q]; ring
  have hKn : quadratic lam (z-c.1)-(bumpData lam d h t).S-(u+q) = K := by dsimp [bumpData,K,q]; ring
  have hxn : (bumpData lam d h t).phi c.2.1 = d.phi c.2.1 := by simp [bumpData,hx]
  have hyn : (bumpData lam d h t).phi c.2.2 = d.phi c.2.2 := by simp [bumpData,hy]
  have hD : 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam) R P :=
    lt_trans (by norm_num) (hd.determinant_positive hc)
  have hDn : 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam) (R+dR) (P+q) := by
    have hh := lt_trans (by norm_num : (0 : ℝ) < 3/100) (hdn.determinant_positive hc)
    change 0 < Certificates.Control.det (2*lam-c.2.1) (c.1+c.2.2-lam)
      (primitive lam (bumpData lam d h t) c.1)
      (quadratic lam (1-c.1)-(bumpData lam d h t).S) at hh
    rwa [hRn,hPn] at hh
  have hAlpha := hd.near_line_alpha_positive hc hz huLow huHigh hfx hfy hnear
  have hA : 0 ≤ Certificates.Control.alphaNumerator (2*lam-c.2.1) (c.1+c.2.2-lam)
      (d.phi c.2.1) (d.phi c.2.2) := by
    have ha := (lt_div_iff₀ hD).mp hAlpha
    change 0 ≤ (c.1+c.2.2-lam)*d.phi c.2.1+(2*lam-c.2.1)*d.phi c.2.2
    simpa only [zero_mul] using ha.le
  have hcy := (hd.control_coefficients_positive hc hz huLow huHigh).2
  have hratio := hd.control_coefficient_ratio hc hz huHigh
  have hv := bumpRatio_gt hd.1 hc.1
  have hcy0 : 0 ≤ Certificates.Control.cy (z-lam) (2*lam-c.2.1) P K := by
    dsimp [P,K]
    linarith
  have hr : Certificates.Control.cx (z-lam) (c.1+c.2.2-lam) R K ≤
      v*Certificates.Control.cy (z-lam) (2*lam-c.2.1) P K := by
    have hh := mul_le_mul_of_nonneg_right hv.le hcy0
    exact hratio.le.trans hh
  rw [controlH_eq_certified_value, controlH_eq_certified_value]
  rw [hRn,hPn,hKn,hxn,hyn]
  exact Certificates.Control.value_RP_shift_nondecreasing (z-lam) (2*lam-c.2.1)
    (c.1+c.2.2-lam) R P K (d.phi c.2.1) (d.phi c.2.2) dR q v hD hDn hA hcy0 hq hdR hr

end OptimalG.Variational
