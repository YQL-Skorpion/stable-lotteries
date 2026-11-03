import OptimalG.BinaryNearOne

/-! Genuine integral/primitive envelopes for the finite C.18 checks. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def binarySlackArea (phi : ℝ → ℝ) (lam S r : ℝ) : ℝ :=
  curvePrimitive phi r-Variational.quadratic lam r+S

noncomputable def binaryAreaUpper (k pref epsArea epsScore r : ℝ) : ℝ :=
  epsArea+epsScore*max (pref-r) 0+k/2*(max (pref-r) 0)^2

private theorem slack_line_integral (k pref epsScore r : ℝ) :
    (∫ u in r..pref,epsScore+k*(pref-u))=
      epsScore*(pref-r)+k/2*(pref-r)^2 := by
  let F := fun u : ℝ => epsScore*u-k/2*(pref-u)^2
  have hd (u : ℝ) : HasDerivAt F (epsScore+k*(pref-u)) u := by
    convert! ((hasDerivAt_id u).const_mul epsScore).sub
      ((((hasDerivAt_const u pref).sub (hasDerivAt_id u)).pow 2).const_mul (k/2)) using 1 <;>
      first | rfl | (funext x; dsimp [F]; ring) | (simp only [Pi.sub_apply,id_eq,zero_sub,mul_one,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => epsScore+k*(pref-u))).intervalIntegrable r pref)]
  dsimp [F]
  ring

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem binarySlackArea_difference {S a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
    binarySlackArea phi lam S a-binarySlackArea phi lam S b=
      ∫ r in a..b,scoreDefect phi lam r := by
  rw [h.scoreDefect_integral ha hab hb]
  unfold binarySlackArea
  ring

theorem binarySlackArea_antitone (S : ℝ) :
    AntitoneOn (binarySlackArea phi lam S) (Icc 0 1) := by
  intro a ha b hb hab
  have hi := intervalIntegral.integral_nonneg (μ:=volume) hab
    (fun r hr => h.scoreDefect_nonneg ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩)
  rw [←h.binarySlackArea_difference (S:=S) ha.1 hab hb.2] at hi
  linarith

/-- A forward score-slope cone gives a second, independent upper bound on
remaining slack area. It is especially useful near the cap contact. -/
theorem binarySlackArea_forward_upper {c r S k : ℝ}
    (hc : 0≤c) (hcr : c≤r) (hr : r≤1)
    (hfall : ∀ u ∈ Icc c r,scoreDefect phi lam c-scoreDefect phi lam u≤k*(u-c)) :
    binarySlackArea phi lam S r≤binarySlackArea phi lam S c-
      scoreDefect phi lam c*(r-c)+k/2*(r-c)^2 := by
  have hi := (h.scoreDefect_continuous.mono (Icc_subset_Icc hc hr)).intervalIntegrable_of_Icc (μ:=volume) hcr
  have hline : (∫ u in c..r,scoreDefect phi lam c+k*(c-u))=
      scoreDefect phi lam c*(r-c)-k/2*(r-c)^2 := by
    have he : (fun u : ℝ => scoreDefect phi lam c+k*(c-u))=
        (fun u => (scoreDefect phi lam c-k*(r-c))+k*(r-u)) := by funext u; ring
    rw [he,slack_line_integral]
    ring
  have hh := intervalIntegral.integral_mono_on hcr
    ((by fun_prop : Continuous (fun u : ℝ => scoreDefect phi lam c+k*(c-u))).intervalIntegrable c r)
    hi (fun u hu => by have hh := hfall u hu; linarith only [hh])
  rw [hline,←h.binarySlackArea_difference (S:=S) hc hcr hr] at hh
  linarith only [hh]

/-- D.3's upper area envelope follows by integrating the actual finite slope
bound backward from the reference rank. -/
theorem binarySlackArea_upper {c t pref k S epsArea epsScore : ℝ}
    (hc0 : 0≤c) (ht1 : t≤1) (hpref : pref ∈ Icc c t)
    (harea : binarySlackArea phi lam S pref≤epsArea)
    (hscore : scoreDefect phi lam pref≤epsScore)
    (hfall : ∀ r ∈ Icc c pref,scoreDefect phi lam r-scoreDefect phi lam pref≤k*(pref-r)) :
    ∀ r ∈ Icc c t,binarySlackArea phi lam S r≤binaryAreaUpper k pref epsArea epsScore r := by
  intro r hr
  by_cases hrp : r≤pref
  · have hi := (h.scoreDefect_continuous.mono
      (Icc_subset_Icc (hc0.trans hr.1) (hpref.2.trans ht1))).intervalIntegrable_of_Icc (μ:=volume) hrp
    have hh := intervalIntegral.integral_mono_on hrp hi
      ((by fun_prop : Continuous (fun u : ℝ => epsScore+k*(pref-u))).intervalIntegrable r pref)
      (fun u hu => by have hh := hfall u ⟨hr.1.trans hu.1,hu.2⟩; linarith only [hh,hscore])
    rw [slack_line_integral,←h.binarySlackArea_difference (S:=S) (hc0.trans hr.1) hrp (hpref.2.trans ht1)] at hh
    unfold binaryAreaUpper
    rw [max_eq_left (sub_nonneg.mpr hrp)]
    linarith only [hh,harea]
  · have hh := h.binarySlackArea_antitone S
      ⟨hc0.trans hpref.1,hpref.2.trans ht1⟩ ⟨hc0.trans hr.1,hr.2.trans ht1⟩ (le_of_not_ge hrp)
    unfold binaryAreaUpper
    rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hrp))]
    simpa using hh.trans harea

/-- A finite rational residual involving lower and upper area envelopes gives
the actual normalized binary test. The interval integral is eliminated by its
proved primitive identity, not supplied as an extra certificate premise. -/
theorem binary_of_area_residual {S q d K low high : ℝ}
    (hd : d ∈ Ioo (0:ℝ) 1) (hq : 0≤q) (hql : q≤lam) (hqd : q+d≤1)
    (hlower : low≤binarySlackArea phi lam S q)
    (hupper : binarySlackArea phi lam S (q+d)≤high)
    (hk : binaryKappa phi d≤K)
    (hcheck : d^2*(K*(lam-q)-1/2)≤low-high) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  have harea : d^2*(K*(lam-q)-1/2)≤∫ r in q..q+d,scoreDefect phi lam r := by
    rw [←h.binarySlackArea_difference (S:=S) hq (by linarith [hd.1]) hqd]
    linarith only [hcheck,hlower,hupper]
  have hdiv : K*(lam-q)-1/2≤(∫ r in q..q+d,scoreDefect phi lam r)/d^2 :=
    (le_div_iff₀ (sq_pos_of_pos hd.1)).mpr (by nlinarith only [harea])
  have hm := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hql)
  apply h.nearOne_binary_of_normalized hd.1 hd.2 hq hqd
  change _-binaryKappa phi d*(lam-q)+1/2≥0
  linarith only [hdiv,hm]

end VerifierCurve

/-- The finite affine majorant of (1-d)κ(d) follows from two scalar
coefficients of the actual quadratic completion. -/
theorem binaryKappa_affine_majorant {phi : ℝ → ℝ} {z Y H d B C : ℝ}
    (hz : z≠1) (hd : d ∈ Ioo (0:ℝ) 1)
    (htail : curvePrimitive phi (1-d)=tailPrimitive z Y H (1-d))
    (hB : tailBackwardSlope z Y H/2-1≤B)
    (hC : C≤tailBackwardCurvature z Y H/3) :
    binaryKappa phi d≤(B-C*d)/(1-d) := by
  rw [binaryKappa_polynomial hz hd.1.ne' (ne_of_lt hd.2) htail]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hd.2).le
  have hh := mul_le_mul_of_nonneg_right hC hd.1.le
  nlinarith only [hh,hB]

end OptimalG
