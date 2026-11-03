import OptimalG.BinaryShapeLocalization
import OptimalG.HeadStationaryCurve
import OptimalG.HeadBarrierComparison

/-! The geometric hypotheses used by C.3 are properties of the actual score
and primitive. No binary test or maximizer statement is included here. -/
namespace OptimalG
open Set Variational

structure BinaryCurveGeometry (phi : ℝ → ℝ) (lam S slope c : ℝ) : Prop where
  lambda_mem : lam ∈ Icc (562325/1000000:ℝ) (562330/1000000:ℝ)
  contact_mem : c ∈ Icc (1459/5000:ℝ) (61/200:ℝ)
  head : ∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),phi r=phi 0+slope*r
  cap_primitive : ∀ r ∈ Icc (527/2000:ℝ) c,curvePrimitive phi r=cap lam S r
  cap_score : ∀ r ∈ Icc (527/2000:ℝ) c,phi r=capScore lam S r
  cap_upper : ∀ r ∈ Icc (0:ℝ) (53/100:ℝ),curvePrimitive phi r≤cap lam S r
  line_score : ∀ r ∈ Icc (7189/20000:ℝ) (31/40:ℝ),phi r=lam-r
  line_primitive : ∀ r ∈ Icc (7189/20000:ℝ) (31/40:ℝ),curvePrimitive phi r=quadratic lam r-S
  pre_slope : ∀ a ∈ Icc (0:ℝ) c,∀ b ∈ Icc (0:ℝ) c,a≤b → slope*(b-a)≤phi b-phi a
  post_slope : ∀ a ∈ Icc c 1,∀ b ∈ Icc c 1,a≤b → phi b-phi a≤(-691/1000)*(b-a)
  head_slope : -691/1000≤slope
  cap_slope : ∀ a ∈ Icc (527/2000:ℝ) c,∀ b ∈ Icc (527/2000:ℝ) c,a≤b →
    (-691/1000)*(b-a)≤phi b-phi a
  low_slope : ∀ a b,0≤a → a≤b → b≤lam → a-b≤phi b-phi a

namespace BinaryCurveGeometry
variable {phi : ℝ → ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

/-- Slack is antitone on the entire low and straight portion. -/
theorem defect_antitone : AntitoneOn (scoreDefect phi lam) (Icc (0:ℝ) (31/40:ℝ)) := by
  intro a ha b hb hab
  have hl0 : 0≤lam := by linarith only [g.lambda_mem.1]
  have hlt : 7189/20000≤lam := by linarith only [g.lambda_mem.1]
  have hlz : lam≤31/40 := by linarith only [g.lambda_mem.2]
  by_cases hbl : b≤lam
  · have hh := g.low_slope a b ha.1 hab hbl
    unfold scoreDefect
    linarith only [hh]
  · have hbline := g.line_score b ⟨hlt.trans (le_of_not_ge hbl),hb.2⟩
    by_cases hal : a≤lam
    · have hh := g.low_slope a lam ha.1 hal le_rfl
      rw [g.line_score lam ⟨hlt,hlz⟩] at hh
      unfold scoreDefect
      rw [hbline]
      linarith only [hh]
    · have haline := g.line_score a ⟨hlt.trans (le_of_not_ge hal),ha.2⟩
      unfold scoreDefect
      rw [haline,hbline]
      ring_nf
      rfl

/-- The actual post-contact score slope supplies the C.17/C.19 slack slope. -/
theorem defect_fall {a b : ℝ} (ha : a ∈ Icc c (7189/20000:ℝ))
    (hb : b ∈ Icc c (7189/20000:ℝ)) (hab : a≤b) :
    scoreDefect phi lam a-scoreDefect phi lam b≤(309/1000)*(b-a) := by
  have hh := g.post_slope a ⟨ha.1,by linarith only [ha.2]⟩
    b ⟨hb.1,by linarith only [hb.2]⟩ hab
  unfold scoreDefect
  linarith only [hh]

/-- The actual geometric package and the explicit small/central scalar
checks cover every split through mass .775. -/
theorem binary_small_central (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hn : BinarySmallIntervals lam S (phi 0) slope (527/2000) c)
    (harea : binarySlackArea phi lam S (348541/1000000)≤87/1000000000)
    (hscore : scoreDefect phi lam (348541/1000000)≤24/100000) :
    ∀ p ∈ Ioc (0:ℝ) (31/40:ℝ),∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hl : lam ∈ Icc (1/2:ℝ) (3/5:ℝ) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hflat : ∀ r ∈ Icc (9/25:ℝ) (31/40:ℝ),curvePrimitive phi r=quadratic lam r-S :=
    fun r hr => g.line_primitive r ⟨by linarith only [hr.1],hr.2⟩
  have hcap : ∀ r ∈ Icc (527/2000:ℝ) (53/100:ℝ),curvePrimitive phi r≤cap lam S r :=
    fun r hr => g.cap_upper r ⟨by linarith only [hr.1],hr.2⟩
  have hmid := h.binary_central_upper_area (S:=S) (c:=c)
    (by linarith only [g.contact_mem.1]) (by linarith only [g.contact_mem.2])
    (g.cap_primitive c ⟨by linarith only [g.contact_mem.1],le_rfl⟩)
    (g.cap_score c ⟨by linarith only [g.contact_mem.1],le_rfl⟩) harea hscore (fun a ha b hb hab => by
      have hh := g.post_slope a ⟨ha.1,by linarith only [ha.2]⟩
        b ⟨hb.1,by linarith only [hb.2]⟩ hab
      unfold scoreDefect
      linarith only [hh])
  intro p hp
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1,by linarith only [hp.2]⟩
  apply h.binary_all_splits_of_low hc hl.1 hp0
  intro q hq hqp hql
  by_cases hps : p≤13/20
  · exact h.binary_small_low hl (by norm_num : (527/2000:ℝ) ∈ Icc (9/50:ℝ) (7/20:ℝ))
      g.head hflat hcap (fun r hr => by
        have hh := g.low_slope 0 r le_rfl hr.1 hr.2
        linarith only [hh]) hn ⟨hp.1,hps⟩ q hq hqp hql
  · exact h.binary_central_low hl (by norm_num : (527/2000:ℝ) ∈ Icc (9/50:ℝ) (7/20:ℝ))
      g.head hflat hcap (fun r hr => g.line_score r ⟨by linarith only [hr.1],hr.2⟩)
      g.low_slope hmid hn ⟨le_of_not_ge hps,hp.2⟩ q ⟨hq,hql⟩

/-- On the full head/rational stationary mass range, all shift and ordering
conditions in the analytic maximizer lemma follow from the fixed geometry. -/
theorem ratio_max (h : VerifierCurve phi lam) {p r : ℝ}
    (hp : p ∈ Icc (31/40:ℝ) (73/80:ℝ)) (hr : r ∈ Ico (0:ℝ) lam)
    (hrshift : 7189/20000≤r+1-p)
    (hroot : binaryStationaryNumerator phi lam p r=0) :
    ∀ q ∈ Ico (0:ℝ) lam,binaryRatio phi lam p q≤
      max (binaryRatio phi lam p 0) (binaryRatio phi lam p r) := by
  apply h.binaryRatio_max_of_piecewise_score_slopes
    (xh:=527/2000) (c:=c) (t:=7189/20000) (slope:=slope) (theta:=691/1000)
    ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
    (by linarith only [g.lambda_mem.2,hp.1])
    ⟨by norm_num,by linarith only [g.lambda_mem.1]⟩
    (by linarith only [g.contact_mem.1]) (by linarith only [g.contact_mem.2])
    (by linarith only [g.lambda_mem.1])
    (by linarith only [g.contact_mem.2,hp.2])
    (by linarith only [g.contact_mem.1,hp.2]) g.head g.pre_slope (by simpa only [neg_div] using g.post_slope)
    (by simpa only [neg_div] using g.head_slope)
    (by simpa only [neg_div] using g.cap_slope) g.low_slope
    (fun q hq => g.line_score q ⟨hq.1,by linarith only [hq.2,g.lambda_mem.2]⟩)
    hr hrshift hroot

/-- A certified stationary barrier value controls every split. The rank-zero
primitive is computed from the actual affine head. -/
theorem binary_of_stationary_value (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi) {p r V : ℝ}
    (hp : p ∈ Icc (31/40:ℝ) (73/80:ℝ)) (hr : r ∈ Ico (0:ℝ) lam)
    (hrshift : 7189/20000≤r+1-p)
    (hroot : binaryStationaryNumerator phi lam p r=0)
    (hratio : binaryRatio phi lam p r=V)
    (hzero : (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*V)
    (hvalue : p*V≤curvePrimitive phi p) :
    ∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨by linarith only [hp.1],by linarith only [hp.2]⟩
  have hheadJ : curvePrimitive phi (1-p)=(phi 0)*(1-p)+slope*(1-p)^2/2 :=
    h.affine_head_primitive g.head ⟨by linarith only [hp.2],by linarith only [hp.1]⟩
  have hz0 : p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p := by
    rw [hheadJ]
    have h1 := mul_le_mul_of_nonneg_left hzero hp0.1.le
    have h2 := mul_le_mul_of_nonneg_left hvalue h.lam_pos.le
    nlinarith only [h1,h2]
  have hmax := g.ratio_max h hp hr hrshift hroot
  have hzeroRatio : binaryRatio phi lam p 0≤curvePrimitive phi p/p := by
    unfold binaryRatio
    have he : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    simp only [zero_add,he,sub_zero]
    exact (div_le_div_iff₀ h.lam_pos hp0.1).mpr (by nlinarith only [hz0])
  have hrootRatio : binaryRatio phi lam p r≤curvePrimitive phi p/p := by
    rw [hratio]
    exact (le_div_iff₀ hp0.1).mpr (by nlinarith only [hvalue])
  have hlow := h.binary_above_lam_of_stationary hp0
    (by linarith only [g.lambda_mem.2,hp.1]) hz0
    (fun q hq _ => (hmax q ⟨hq.1.le,hq.2⟩).trans (max_le hzeroRatio hrootRatio))
  apply h.binary_all_splits_of_low hc (by linarith only [g.lambda_mem.1]) hp0
  intro q hq hqp hql
  exact hlow q ⟨hq,hql⟩

/-- A matching head rank is an actual stationary zero; the shifted rank is
proved to lie on the completed line segment. -/
theorem head_root (h : VerifierCurve phi lam) {p r : ℝ}
    (hp : p ∈ Icc (31/40:ℝ) (17/20:ℝ)) (hr : r ∈ Icc (0:ℝ) (527/2000:ℝ))
    (hrshift : 7189/20000≤r+1-p)
    (hmatch : headStationaryLevel lam S (phi 0) slope r=(1-p)^2) :
    binaryStationaryNumerator phi lam p r=0 := by
  have hh : r+1-p ∈ Icc (7189/20000:ℝ) (31/40:ℝ) :=
    ⟨hrshift,by linarith only [hr.2,hp.1]⟩
  exact headStationary_actual_root (h.affine_head_primitive g.head hr) (g.head r hr)
    (g.line_primitive _ hh) (g.line_score _ hh) hmatch

/-- Finite head scalar comparisons and actual geometry give an upper envelope
of every original terminal test, with no hypothesis on J(p) or Y(p). -/
theorem terminal_le_head (h : VerifierCurve phi lam) {p r q : ℝ}
    (hp : p ∈ Icc (31/40:ℝ) (17/20:ℝ)) (hr : r ∈ Icc (0:ℝ) (527/2000:ℝ))
    (hq : q ∈ Icc (26/100:ℝ) (31/100:ℝ))
    (hrshift : 7189/20000≤r+1-p)
    (hmatch : headStationaryLevel lam S (phi 0) slope r=(1-p)^2)
    (hzero : (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-headSlack lam (phi 0) slope r)) :
    terminalBound lam S p q≤p*((1-p)-headSlack lam (phi 0) slope r) := by
  have hrl : r<lam := by linarith only [hr.2,g.lambda_mem.1]
  have hql : q<lam := by linarith only [hq.2,g.lambda_mem.1]
  have hroot := g.head_root h hp hr hrshift hmatch
  have hrline := g.line_score (r+1-p) ⟨hrshift,by linarith only [hr.2,hp.1]⟩
  have hratio : binaryRatio phi lam p r=(1-p)-headSlack lam (phi 0) slope r := by
    rw [h.binaryRatio_eq_deficit hrl hroot hrline,g.head r hr]
    rfl
  have hzeroRatio : binaryRatio phi lam p 0≤binaryRatio phi lam p r := by
    rw [hratio]
    unfold binaryRatio
    simp only [zero_add,sub_zero]
    have hJ0 : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    rw [hJ0,sub_zero,h.affine_head_primitive g.head
      (show 1-p ∈ Icc (0:ℝ) (527/2000:ℝ) from ⟨by linarith only [hp.2],by linarith only [hp.1]⟩)]
    exact (div_le_iff₀ h.lam_pos).mpr (by nlinarith only [hzero])
  have hmax := g.ratio_max h ⟨hp.1,by linarith only [hp.2]⟩ ⟨hr.1,hrl⟩ hrshift hroot
    q ⟨by linarith only [hq.1],hql⟩
  rw [max_eq_right hzeroRatio,hratio] at hmax
  have hcap := g.cap_upper q ⟨by linarith only [hq.1],by linarith only [hq.2]⟩
  have hshift := g.line_primitive (q+1-p)
    ⟨by linarith only [hq.1,hp.2],by linarith only [hq.2,hp.1]⟩
  exact (terminalBound_le_actual_binaryRatio (by linarith only [hp.1]) hql hcap hshift).trans
    (mul_le_mul_of_nonneg_left hmax (by linarith only [hp.1]))

/-- Alternative comparison once a completed curve is already available.
For constructing that curve without a circular contact-location argument,
use `original_contact_after_head_entry`, which does not assume this geometry. -/
theorem contact_after_head_entry (h : VerifierCurve phi lam)
    {Y dY : ℝ → ℝ} {b z q pf theta alpha : ℝ}
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ))
    (hY : ContinuousOn Y (Icc (31/40:ℝ) b))
    (hYd : ∀ p ∈ Ioo (31/40:ℝ) b,HasDerivAt Y (dY p) p)
    (hleft : (1-31/40:ℝ)^2≤headStationaryLevel lam S (phi 0) slope 0)
    (hentry : headStationaryLevel lam S (phi 0) slope (527/2000)=(1-b)^2)
    (hterminal : terminalBound lam S b (527/2000)≤Y b)
    (hdeficit : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),
      quadratic lam p-S-Y p≤(399/500)*(max (p-391/500) 0)^2)
    (hshift : ∀ p ∈ Icc (31/40:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 → 7189/20000≤r+1-p)
    (hzero : ∀ p ∈ Icc (31/40:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-headSlack lam (phi 0) slope r))
    (hearly : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      p*((1-p)-headSlack lam (phi 0) slope r)<
        quadratic lam p-S-(399/500)*(max (p-391/500) 0)^2)
    (hcontrol : ∀ p ∈ Ioo (807/1000:ℝ) b,dY p≤highAffineControl lam S pf theta alpha Y p)
    (hlate : ∀ p ∈ Ioo (807/1000:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      -theta*(p-lam)-alpha*(quadratic lam (p-pf)-S-p*((1-p)-headSlack lam (phi 0) slope r))<
        1-2*p-headSlack lam (phi 0) slope r+p*(1-p)/(lam-r))
    (hz : z ∈ Icc (21/25:ℝ) (7/8:ℝ))
    (hq : q ∈ Icc (26/100:ℝ) (31/100:ℝ))
    (hcontact : terminalBound lam S z q=Y z) : b≤z := by
  have hxl : (527/2000:ℝ)<lam := by linarith only [g.lambda_mem.1]
  have hs : 0<1+slope := by linarith only [g.head_slope]
  obtain ⟨r,K,hr,hrlip,hrd⟩ := exists_head_stationary_branch
    (by norm_num : (0:ℝ)≤527/2000) hxl hs (by norm_num : (0:ℝ)≤31/40)
    (by linarith only [hb.1] : (31/40:ℝ)≤b) (by linarith only [hb.2] : b≤1)
    hleft hentry.le
  have hjoin : cap lam S (527/2000)=(phi 0)*(527/2000)+slope*(527/2000)^2/2 := by
    rw [←g.cap_primitive (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩]
    exact h.affine_head_primitive g.head ⟨by norm_num,le_rfl⟩
  have hgap := head_barrier_initial_gap (a:=31/40) (m:=807/1000)
    (by norm_num) (by linarith only [hb.1]) hY hrlip.continuousOn hYd
    (fun p hp => (hr p hp).2) (fun p hp => (hr p hp).1) hxl hs hentry hjoin hterminal
    hdeficit hearly hcontrol hlate
  apply terminal_contact_after_head_entry (a:=31/40) (by linarith only [hz.1]) hcontact hgap
  intro p hp
  have hpr : p ∈ Icc (31/40:ℝ) b := ⟨hp.1,hp.2.le⟩
  exact g.terminal_le_head h ⟨hp.1,by linarith only [hp.2,hb.2]⟩ (hr p hpr).1 hq
    (hshift p hpr (r p) (hr p hpr).1 (hr p hpr).2) (hr p hpr).2
    (hzero p hpr (r p) (hr p hpr).1 (hr p hpr).2)

end BinaryCurveGeometry
end OptimalG
