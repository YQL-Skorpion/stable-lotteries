import OptimalG.BinaryExplicitProfiles
import OptimalG.BinaryCurveGeometry
import OptimalG.BinaryKappaBounds

/-! Every binary test from mass .9125 to one is reduced to explicit finite
rational/cone residuals. Integrals, smaller widths and rank coverage are proved. -/
namespace OptimalG
open Set Variational

/-- All fields are finite-domain scalar expressions built from the displayed
head, cap and cone formulas. They contain no unknown score, primitive or binary test. -/
structure BinaryLateIntervals (lam S phi0 slope c pref epsArea epsScore B C : ℝ) (n : ℕ) : Prop where
  samples_pos : 0<n
  bound_nonneg : 0≤B
  width_nonneg : ∀ d ∈ Icc (1/50:ℝ) (7/80:ℝ),0≤(B-C*d)/(1-d)
  width_high : ∀ d ∈ Icc (1/50:ℝ) (7/80:ℝ),((B-C*d)/(1-d))*(lam-337/1000)≤1/2
  area : ∀ d ∈ Icc (1/50:ℝ) (7/80:ℝ),∀ q ∈ Icc (0:ℝ) (337/1000:ℝ),
    d^2*(((B-C*d)/(1-d))*(lam-q)-1/2)≤
      binaryAreaLower lam S phi0 slope (527/2000) c (7189/20000) (309/1000) q-
      binaryAreaUpperProfile lam S phi0 slope (527/2000) c (309/1000) pref epsArea epsScore (q+d)
  small_rank : B*lam≤50*binaryScoreLower lam S phi0 slope (527/2000) c (7189/20000) (309/1000) (27/100)+1/2
  high_rank : B*(lam-337/1000)≤1/2
  right_sum : ∀ q ∈ Icc (1/4:ℝ) (337/1000:ℝ),
    0≤2500*(∑ i ∈ Finset.range n,(1/(50*(n:ℝ)))*
      binaryScoreLower lam S phi0 slope (527/2000) c (7189/20000) (309/1000)
        (q+((i:ℝ)+1)/(50*(n:ℝ))))-B*(lam-q)+1/2

namespace BinaryCurveGeometry
variable {phi : ℝ → ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

/-- Concrete D3 area/score bounds and the polynomial tail coefficients imply
all near-terminal binary inequalities, not merely sampled inequalities. -/
theorem binary_late_all (h : VerifierCurve phi lam)
    {pref epsArea epsScore B C z Y H : ℝ} {n : ℕ}
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hs : 0<capSlack lam S c)
    (hpref : pref ∈ Icc c (7189/20000:ℝ))
    (harea : binarySlackArea phi lam S pref≤epsArea)
    (hscore : scoreDefect phi lam pref≤epsScore)
    (hz : z<1)
    (htail : ∀ p ∈ Ico (73/80:ℝ) 1,curvePrimitive phi p=tailPrimitive z Y H p)
    (hA : tailBackwardSlope z Y H/2-1≤B)
    (hdecay : tailBackwardSlope z Y H/2-1≤tailBackwardCurvature z Y H/3)
    (haffine : tailBackwardSlope z Y H/2-1-(tailBackwardCurvature z Y H/3)*(7/80)≤B-C*(7/80))
    (checks : BinaryLateIntervals lam S (phi 0) slope c pref epsArea epsScore B C n) :
    ∀ p ∈ Ico (73/80:ℝ) 1,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hct : c≤7189/20000 := by linarith only [g.contact_mem.2]
  have hxc : (527/2000:ℝ)≤c := by linarith only [g.contact_mem.1]
  have hc0 : 0≤c := by linarith only [g.contact_mem.1]
  have ht1 : (7189/20000:ℝ)≤1 := by norm_num
  have htz : (7189/20000:ℝ)≤31/40 := by norm_num
  have hcontact := g.line_primitive (7189/20000) ⟨le_rfl,htz⟩
  have htzero : scoreDefect phi lam (7189/20000)=0 := by
    unfold scoreDefect
    rw [g.line_score (7189/20000) ⟨le_rfl,htz⟩]
    ring
  have hanti := g.defect_antitone.mono (Icc_subset_Icc hc0 htz)
  have hlowArea := h.binaryAreaLower_le (S:=S) (slope:=slope) (xh:=527/2000)
    (c:=c) (t:=7189/20000) (z0:=31/40) (k:=309/1000)
    (by norm_num) hxc hct htz (by norm_num) (by norm_num) hs g.head g.cap_primitive
    (g.cap_score c ⟨hxc,le_rfl⟩) hcontact (g.line_primitive (31/40) ⟨htz,le_rfl⟩)
    htzero hanti (fun a ha b hb hab => g.defect_fall ha hb hab)
  have hlowScore := h.binaryScoreLower_le (S:=S) (slope:=slope) (xh:=527/2000)
    (c:=c) (t:=7189/20000) (z0:=31/40) (k:=309/1000)
    (by norm_num) hxc hct htz (by norm_num) (by norm_num) hs g.head
    (g.cap_primitive c ⟨hxc,le_rfl⟩) g.cap_score hcontact hanti
    (fun a ha b hb hab => g.defect_fall ha hb hab)
  have hupper := h.binaryAreaUpperProfile_ge (S:=S) (slope:=slope) (xh:=527/2000)
    (c:=c) (z0:=31/40) (k:=309/1000)
    (by norm_num) hxc (by norm_num) ⟨hpref.1,hpref.2.trans htz⟩ g.head g.cap_primitive
    harea hscore (fun r hr => g.defect_fall ⟨hr.1,hr.2.trans hpref.2⟩ hpref hr.2)
  have hkSmall : ∀ d ∈ Ioc (0:ℝ) (1/50:ℝ),binaryKappa phi d≤B := by
    intro d hd
    exact binaryKappa_polynomial_upper hz.ne ⟨hd.1,by linarith only [hd.2]⟩
      (htail (1-d) ⟨by linarith only [hd.2],by linarith only [hd.1]⟩) hA
      hdecay
  have hnear := h.binary_near_one_all checks.samples_pos
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩ hc checks.bound_nonneg
    g.defect_antitone hkSmall
    (fun r hr => hlowScore r ⟨by linarith only [hr.1],by linarith only [hr.2]⟩)
    checks.small_rank checks.high_rank checks.right_sum
  intro p hp
  by_cases hpn : 49/50≤p
  · exact hnear p ⟨hpn,hp.2⟩
  · have hd : 1-p ∈ Icc (1/50:ℝ) (7/80:ℝ) :=
      ⟨by linarith only [hpn],by linarith only [hp.1]⟩
    have hd0 : 1-p ∈ Ioo (0:ℝ) 1 := ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
    have hk := binaryKappa_affine_majorant_of_endpoints hz.ne hd0
      (by norm_num : (0:ℝ)<7/80) hd.2
      (by simpa only [sub_sub_cancel] using htail p hp) hA haffine
    have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],hp.2⟩
    apply h.binary_all_splits_of_low hc (by linarith only [g.lambda_mem.1]) hp0
    intro q hq hqp hql
    by_cases hqhi : 337/1000≤q
    · have hh := h.nearOne_binary_high_low_ranks hd0 ⟨hqhi,hql⟩ (by linarith only [hqp])
        (checks.width_nonneg (1-p) hd) hk (checks.width_high (1-p) hd)
      simpa only [sub_sub_cancel,normalizedBinaryTest] using hh
    · have hqb : q ∈ Icc (0:ℝ) (337/1000:ℝ) := ⟨hq,le_of_not_ge hqhi⟩
      have hh := h.binary_of_area_residual hd0 hq hql (by linarith only [hqp])
        (hlowArea q ⟨hq,by linarith only [hqb.2]⟩)
        (hupper (q+(1-p)) ⟨by linarith only [hq,hd0.1],by linarith only [hqb.2,hd.2]⟩)
        hk (checks.area (1-p) hd q hqb)
      simpa only [sub_sub_cancel,normalizedBinaryTest] using hh

end BinaryCurveGeometry
end OptimalG
