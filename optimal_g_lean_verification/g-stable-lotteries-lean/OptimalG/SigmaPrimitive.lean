import OptimalG.SigmaAreaElimination
import OptimalG.NearOneScaling
import OptimalG.DefectBounds

/-! The C.3 slack estimates are connected here to the actual verifier score,
its primitive, and the finite-election binary test. -/
namespace OptimalG
open Set MeasureTheory
/-- The score-slope bounds from the curve's shape theorem give precisely the
finite slack-slope bounds needed by the cone integrals. -/
theorem scoreDefect_shape_of_score_slopes {phi : ℝ → ℝ} {lam k : ℝ} {D : Set ℝ}
    (hlow : ∀ a ∈ D,∀ b ∈ D,a≤b → a-b≤phi b-phi a)
    (hup : ∀ a ∈ D,∀ b ∈ D,a≤b → phi b-phi a≤(k-1)*(b-a)) :
    AntitoneOn (scoreDefect phi lam) D ∧
      ∀ a ∈ D,∀ b ∈ D,a≤b → scoreDefect phi lam a-scoreDefect phi lam b≤k*(b-a) := by
  constructor
  · intro a ha b hb hab
    have hh := hlow a ha b hb hab
    dsimp [scoreDefect]
    linarith
  · intro a ha b hb hab
    have hh := hup a ha b hb hab
    dsimp [scoreDefect]
    nlinarith

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem scoreDefect_continuous : ContinuousOn (scoreDefect phi lam) (Icc 0 1) :=
  (continuous_const.sub continuous_id).continuousOn.sub h.continuous

/-- Integrating the actual slack score gives the exact quadratic-minus-primitive increment. -/
theorem scoreDefect_integral {a b : ℝ} (ha : 0≤a) (hab : a≤b) (hb : b≤1) :
    (∫ r in a..b,scoreDefect phi lam r)=
      Variational.quadratic lam b-Variational.quadratic lam a-
        (curvePrimitive phi b-curvePrimitive phi a) := by
  have hline : IntervalIntegrable (fun r : ℝ => lam-r) volume a b :=
    (continuous_const.sub continuous_id).intervalIntegrable a b
  have hQ : (∫ r in a..b,lam-r)=Variational.quadratic lam b-Variational.quadratic lam a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => Variational.quadratic_hasDerivAt lam r) hline
  change (∫ r in a..b,(lam-r)-phi r)=_
  rw [intervalIntegral.integral_sub hline (h.integral_subinterval ha hab hb),hQ,
    ← h.primitive_difference ha hab hb]

/-- At a contact with the flat slack line, the remaining slack area equals
J(q)-Q(q)+S, with the sign required by C.17--C.19. -/
theorem scoreDefect_tail_integral {q t S : ℝ} (hq : 0≤q) (hqt : q≤t) (ht : t≤1)
    (hcontact : curvePrimitive phi t=Variational.quadratic lam t-S) :
    (∫ r in q..t,scoreDefect phi lam r)=curvePrimitive phi q-Variational.quadratic lam q+S := by
  rw [h.scoreDefect_integral hq hqt ht,hcontact]
  ring

/-- The cone bound itself places the area-defined cutoff before the terminal
contact. This also covers zero-slack ranks to the right of that contact. -/
theorem slack_cutoff_le_contact {c t S k : ℝ}
    (hc0 : 0≤c) (hct : c≤t) (ht1 : t≤1) (hk : 0<k)
    (hs : 0<scoreDefect phi lam c)
    (hcontact : curvePrimitive phi t=Variational.quadratic lam t-S)
    (htzero : scoreDefect phi lam t=0)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c t))
    (hslope : ∀ r ∈ Icc c t,
      scoreDefect phi lam r-scoreDefect phi lam t≤k*(t-r)) :
    c+(curvePrimitive phi c-Variational.quadratic lam c+S)/scoreDefect phi lam c+
      scoreDefect phi lam c/(2*k)≤t := by
  have hh := sigma_prefix_upper hct hk
    (h.scoreDefect_continuous.mono (Icc_subset_Icc hc0 ht1)) hanti hslope
  rw [h.scoreDefect_tail_integral hc0 hct ht1 hcontact,htzero,sub_zero] at hh
  have hdiv : (curvePrimitive phi c-Variational.quadratic lam c+S)/scoreDefect phi lam c≤
      t-c-scoreDefect phi lam c/(2*k) := by
    apply (div_le_iff₀ hs).mpr
    calc
      _≤scoreDefect phi lam c*(t-c)-(scoreDefect phi lam c)^2/(2*k) := hh
      _=(t-c-scoreDefect phi lam c/(2*k))*scoreDefect phi lam c := by ring
  linarith

/-- C.17 for the actual primitive. Its total area is computed from the left
primitive value, rather than supplied as an unrelated scalar. -/
theorem primitive_slack_lower {c t q S k : ℝ}
    (hc0 : 0≤c) (ht1 : t≤1) (hq : q ∈ Icc c t) (hk : 0<k)
    (hs : 0<scoreDefect phi lam c)
    (hcontact : curvePrimitive phi t=Variational.quadratic lam t-S)
    (htzero : scoreDefect phi lam t=0)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c t))
    (hslope : ∀ a ∈ Icc c t,∀ b ∈ Icc c t,a≤b →
      scoreDefect phi lam a-scoreDefect phi lam b≤k*(b-a)) :
    let s := scoreDefect phi lam c
    let x0 := c+(curvePrimitive phi c-Variational.quadratic lam c+S)/s+s/(2*k)
    k/2*((max (x0-q) 0)^2-(max (x0-s/k-q) 0)^2)≤
      curvePrimitive phi q-Variational.quadratic lam q+S := by
  have hh := sigma_integral_lower hq hk hs
    (h.scoreDefect_continuous.mono (Icc_subset_Icc hc0 ht1))
    (fun r hr => h.scoreDefect_nonneg ⟨hc0.trans hr.1,hr.2.trans ht1⟩)
    hanti htzero hslope
  dsimp only at hh ⊢
  rw [h.scoreDefect_tail_integral hc0 (hq.1.trans hq.2) ht1 hcontact,
    h.scoreDefect_tail_integral (hc0.trans hq.1) hq.2 ht1 hcontact] at hh
  exact hh

/-- C.19 for the actual score and actual total primitive slack. -/
theorem score_slack_lower {c t q S k : ℝ}
    (hc0 : 0≤c) (ht1 : t≤1) (hq : q ∈ Icc c t) (hk : 0<k)
    (hs : 0<scoreDefect phi lam c)
    (hcontact : curvePrimitive phi t=Variational.quadratic lam t-S)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c t))
    (hslope : ∀ r ∈ Icc c q,
      scoreDefect phi lam r-scoreDefect phi lam q≤k*(q-r)) :
    let s := scoreDefect phi lam c
    let x0 := c+(curvePrimitive phi c-Variational.quadratic lam c+S)/s+s/(2*k)
    s*max (x0-q) 0/(s/k+t-q)≤scoreDefect phi lam q := by
  have hh := sigma_pointwise_lower hq hk hs
    (h.scoreDefect_continuous.mono (Icc_subset_Icc hc0 ht1))
    (h.scoreDefect_nonneg ⟨hc0.trans hq.1,hq.2.trans ht1⟩) hanti hslope
  dsimp only at hh ⊢
  rw [h.scoreDefect_tail_integral hc0 (hq.1.trans hq.2) ht1 hcontact] at hh
  exact hh

/-- The slack identity used to normalize the two-class inequality. -/
theorem primitive_increment_eq_slack {q d : ℝ} (hq : 0≤q) (hd : 0≤d) (hqd : q+d≤1) :
    curvePrimitive phi (q+d)-curvePrimitive phi q=
      (lam-q)*d-d^2/2-(∫ r in q..q+d,scoreDefect phi lam r) := by
  have hh := h.scoreDefect_integral hq (by linarith) hqd
  dsimp [Variational.quadratic] at hh
  nlinarith

/-- The normalized C.18 test implies the actual binary test for every admissible
split, with positive actual primitive denominator. -/
theorem nearOne_binary_of_normalized {q d : ℝ} (hd : 0<d) (hd1 : d<1)
    (hq : 0≤q) (hqd : q+d≤1)
    (hcheck : 0≤(∫ r in q..q+d,scoreDefect phi lam r)/d^2-
      ((d-curvePrimitive phi (1-d)/(1-d))/d^2)*(lam-q)+1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  have hnorm := (nearOne_binary_iff_normalized hd hd1
    (h.primitive_increment_eq_slack hq hd.le hqd)).mpr hcheck
  have hD : packingDelta phi (1-d) q=curvePrimitive phi (q+d)-curvePrimitive phi q := by
    unfold packingDelta
    congr 2
    ring
  rw [hD]
  have hpos := h.primitive_pos (q:=1-d) ⟨by linarith,by linarith⟩
  have hh : ((1-d)/curvePrimitive phi (1-d))*(curvePrimitive phi (q+d)-curvePrimitive phi q)≤lam-q := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hpos).mpr hnorm
  linarith

/-- A single endpoint integral check controls all smaller widths, including the
actual κ built from the verifier's primitive. -/
theorem nearOne_binary_of_endpoint {q d H upper : ℝ}
    (hd : d ∈ Ioc 0 H) (hd1 : d<1) (hq : 0≤q) (hql : q≤lam) (hqH : q+H≤1)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc q (q+H)))
    (hk : (d-curvePrimitive phi (1-d)/(1-d))/d^2≤upper)
    (hcheck : 0≤(∫ r in q..q+H,scoreDefect phi lam r)/H^2-upper*(lam-q)+1/2) :
    q+((1-d)/curvePrimitive phi (1-d))*packingDelta phi (1-d) q≤lam := by
  apply h.nearOne_binary_of_normalized hd.1 hd1 hq (by linarith [hd.2])
  exact nearOne_test_of_endpoint
    (h.scoreDefect_continuous.mono (Icc_subset_Icc hq hqH))
    (fun r hr => h.scoreDefect_nonneg ⟨hq.trans hr.1,hr.2.trans hqH⟩)
    hanti hd hql hk hcheck

end VerifierCurve
end OptimalG
