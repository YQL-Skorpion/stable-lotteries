import OptimalG.BinaryCurveGeometry
import OptimalG.VerifierPrimitiveCap

/-! Explicit low-rank envelopes used by the extended-mass high test. All
bounds here concern the actual integral primitive of the verifier curve. -/
namespace OptimalG
open Set MeasureTheory Variational

noncomputable def extendedSlackUpper
    (lam S phi0 slope xh c r : ℝ) : ℝ :=
  if r≤xh then quadratic lam r-(phi0*r+slope*r^2/2)
  else if r≤c then quadratic lam r-cap lam S r
  else S-max 0 (capDeficit lam S c-capSlack lam S c*(r-c))

noncomputable def extendedRemainingUpper
    (lam S phi0 slope xh cut pref line k epsArea epsScore r : ℝ) : ℝ :=
  if r≤xh then phi0*r+slope*r^2/2-quadratic lam r+S
  else if r≤cut then capDeficit lam S r
  else if r≤pref then min (capDeficit lam S r)
    (binaryAreaUpper k pref epsArea epsScore r)
  else if r≤line then epsArea else 0

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- Integrating an antitone, nonnegative slack gives the forward lower area
bound used for the cumulative-slack upper envelope. -/
theorem remainingSlack_forward_lower {c r z0 S : ℝ}
    (hc : 0≤c) (hcr : c≤r) (hr : r≤z0) (hz : z0≤1)
    (hanchor : curvePrimitive phi z0=quadratic lam z0-S)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c z0)) :
    max 0 (binarySlackArea phi lam S c-scoreDefect phi lam c*(r-c))≤
      binarySlackArea phi lam S r := by
  have harea0 : 0≤binarySlackArea phi lam S r := by
    have hm := h.binarySlackArea_antitone S ⟨hc.trans hcr,hr.trans hz⟩
      ⟨hc.trans (hcr.trans hr),hz⟩ hr
    have he : binarySlackArea phi lam S z0=0 := by
      unfold binarySlackArea
      rw [hanchor]
      ring
    simpa only [he] using hm
  have hi := (h.scoreDefect_continuous.mono
    (Icc_subset_Icc hc (hr.trans hz))).intervalIntegrable_of_Icc (μ:=volume) hcr
  have hiUpper := intervalIntegral.integral_mono_on hcr hi
    (intervalIntegrable_const (c:=scoreDefect phi lam c))
    (fun u hu => hanti ⟨le_rfl,hcr.trans hr⟩ ⟨hu.1,hu.2.trans hr⟩ hu.1)
  rw [←h.binarySlackArea_difference (S:=S) hc hcr (hr.trans hz)] at hiUpper
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hiUpper
  exact max_le harea0 (by nlinarith only [hiUpper])

end VerifierCurve

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

/-- The cap anchor at .2918 is below the actual contact; no identification
of the unknown contact with a numerical endpoint is made. -/
theorem slackUpper_bound (h : VerifierCurve phi lam) {q : ℝ}
    (hq : q∈Icc (0:ℝ) lam) :
    quadratic lam q-curvePrimitive phi q≤
      extendedSlackUpper lam S (phi 0) slope (527/2000) (1459/5000) q := by
  by_cases hqh : q≤527/2000
  · rw [extendedSlackUpper,if_pos hqh,h.affine_head_primitive g.head ⟨hq.1,hqh⟩]
  · by_cases hqc : q≤1459/5000
    · rw [extendedSlackUpper,if_neg hqh,if_pos hqc,
        g.cap_primitive q ⟨le_of_not_ge hqh,hqc.trans g.contact_mem.1⟩]
    · have hcJ := g.cap_primitive (1459/5000)
        ⟨by norm_num,g.contact_mem.1⟩
      have hcScore := g.cap_score (1459/5000)
        ⟨by norm_num,g.contact_mem.1⟩
      have hzJ := g.line_primitive (31/40) ⟨by norm_num,le_rfl⟩
      have hlow := h.remainingSlack_forward_lower (c:=1459/5000) (r:=q)
        (z0:=31/40) (by norm_num) (le_of_not_ge hqc)
        (by linarith only [hq.2,g.lambda_mem.2]) (by norm_num) hzJ
        (g.defect_antitone.mono (Icc_subset_Icc (by norm_num) le_rfl))
      rw [extendedSlackUpper,if_neg hqh,if_neg hqc]
      have he : binarySlackArea phi lam S (1459/5000)=capDeficit lam S (1459/5000) := by
        unfold binarySlackArea capDeficit
        rw [hcJ]
        ring
      have hs : scoreDefect phi lam (1459/5000)=capSlack lam S (1459/5000) := by
        unfold scoreDefect capSlack
        rw [hcScore]
      rw [he,hs] at hlow
      unfold binarySlackArea at hlow
      linarith only [hlow]

/-- The remaining-area upper envelope combines the cap, the actual reference
area and score, the integrated post-contact slope, and the line anchor. -/
theorem remainingUpper_bound (h : VerifierCurve phi lam)
    {pref epsArea epsScore r : ℝ}
    (hpref : pref∈Icc (313/1000:ℝ) (9/25))
    (harea : binarySlackArea phi lam S pref≤epsArea)
    (hscore : scoreDefect phi lam pref≤epsScore)
    (hr : r∈Icc (0:ℝ) 1) :
    binarySlackArea phi lam S r≤
      extendedRemainingUpper lam S (phi 0) slope (527/2000) (313/1000) pref
        (9/25) (309/1000) epsArea epsScore r := by
  have hcapBound {u : ℝ} (hu : u∈Icc (0:ℝ) (53/100)) :
      binarySlackArea phi lam S u≤capDeficit lam S u := by
    have hh := g.cap_upper u hu
    unfold binarySlackArea capDeficit
    linarith only [hh]
  by_cases hrh : r≤527/2000
  · rw [extendedRemainingUpper,if_pos hrh,binarySlackArea,
      h.affine_head_primitive g.head ⟨hr.1,hrh⟩]
  · by_cases hrc : r≤313/1000
    · rw [extendedRemainingUpper,if_neg hrh,if_pos hrc]
      exact hcapBound ⟨hr.1,by linarith only [hrc]⟩
    · by_cases hrp : r≤pref
      · rw [extendedRemainingUpper,if_neg hrh,if_neg hrc,if_pos hrp]
        apply le_min (hcapBound ⟨hr.1,by linarith only [hrp,hpref.2]⟩)
        apply h.binarySlackArea_upper (c:=313/1000) (t:=9/25)
          (by norm_num) (by norm_num) hpref harea hscore _ r
          ⟨le_of_not_ge hrc,hrp.trans hpref.2⟩
        intro u hu
        have hh := g.post_slope u
          ⟨by linarith only [g.contact_mem.2,hu.1],by linarith only [hu.2,hpref.2]⟩
          pref ⟨by linarith only [g.contact_mem.2,hpref.1],by linarith only [hpref.2]⟩ hu.2
        unfold scoreDefect
        linarith only [hh]
      · by_cases hrl : r≤9/25
        · rw [extendedRemainingUpper,if_neg hrh,if_neg hrc,if_neg hrp,if_pos hrl]
          exact (h.binarySlackArea_antitone S
            ⟨by linarith only [hpref.1],by linarith only [hpref.2]⟩ hr
            (le_of_not_ge hrp)).trans harea
        · rw [extendedRemainingUpper,if_neg hrh,if_neg hrc,if_neg hrp,if_neg hrl]
          have hh := h.primitive_le_quadratic_after_anchor (a:=9/25)
            (by norm_num) (g.line_primitive (9/25) ⟨by norm_num,by norm_num⟩)
            r ⟨le_of_not_ge hrl,hr.2⟩
          unfold binarySlackArea
          linarith only [hh]

end BinaryCurveGeometry
end OptimalG
