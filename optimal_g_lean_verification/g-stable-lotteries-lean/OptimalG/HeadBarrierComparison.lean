import OptimalG.HeadStationaryCurve
import OptimalG.VariationalCapControl
import OptimalG.HighContinuationShape
import OptimalG.TailContact

/-! The affine-head barrier is compared with the original continuation before
any quadratic tail is attached. This avoids assuming the contact location. -/
namespace OptimalG
open Set
open Variational (quadratic cap terminalBound)

/-- The scalar head stationary barrier dominates its entire rational ratio
by a square. This identity does not mention the completed curve. -/
theorem head_terminal_gap_identity {lam S phi0 slope p q r : ℝ}
    (hql : q≠lam)
    (hmatch : headStationaryLevel lam S phi0 slope r=(1-p)^2) :
    p*((1-p)-headSlack lam phi0 slope r)-terminalBound lam S p q=
      p*((1+slope)*(q-r)^2/2+cap lam S q-(phi0*q+slope*q^2/2))/(lam-q) := by
  have he : quadratic lam (1-p+q)-S-cap lam S q=
      (lam-q)*((1-p)-headSlack lam phi0 slope r)-
        ((1+slope)*(q-r)^2/2+cap lam S q-(phi0*q+slope*q^2/2)) := by
    unfold quadratic headSlack
    unfold headStationaryLevel headStationaryConstant at hmatch
    nlinarith only [hmatch]
  unfold terminalBound
  rw [he]
  have hden : lam-q≠0 := sub_ne_zero.mpr hql.symm
  field_simp
  ring

/-- A scalar cap-versus-head bound suffices for original terminal domination;
no completed-score shape or tail property is used. -/
theorem terminalBound_le_head_scalar {lam S phi0 slope p q r : ℝ}
    (hp : 0≤p) (hql : q<lam) (hs : 0≤1+slope)
    (hcap : phi0*q+slope*q^2/2≤cap lam S q)
    (hmatch : headStationaryLevel lam S phi0 slope r=(1-p)^2) :
    terminalBound lam S p q≤p*((1-p)-headSlack lam phi0 slope r) := by
  have hh := head_terminal_gap_identity (ne_of_lt hql) hmatch
  have hnum : 0≤(1+slope)*(q-r)^2/2+cap lam S q-(phi0*q+slope*q^2/2) := by
    have hx := div_nonneg (mul_nonneg hs (sq_nonneg (q-r))) (by norm_num : (0:ℝ)≤2)
    linarith only [hx,hcap]
  have hn := div_nonneg (mul_nonneg hp hnum) (sub_pos.mpr hql).le
  linarith only [hh,hn]

/-- Tangency and finite cap-score slopes put the head primitive below cap
on both sides of its join. -/
theorem head_cap_gap_nonneg {lam S phi0 slope a b xh : ℝ}
    (hx : xh ∈ Icc a b) (hb1 : b<1)
    (hjoin : cap lam S xh=phi0*xh+slope*xh^2/2)
    (hscore : Variational.capScore lam S xh=phi0+slope*xh)
    (hcapSlope : ∀ u ∈ Icc a b,∀ v ∈ Icc a b,u≤v →
      slope*(v-u)≤Variational.capScore lam S v-Variational.capScore lam S u) :
    ∀ q ∈ Icc a b,phi0*q+slope*q^2/2≤cap lam S q := by
  let F := fun q : ℝ => cap lam S q-(phi0*q+slope*q^2/2)
  have hFd (q : ℝ) (hq : q ∈ Icc a b) :
      HasDerivAt F (Variational.capScore lam S q-(phi0+slope*q)) q := by
    convert! (Variational.cap_hasDerivAt lam S q (ne_of_lt (hq.2.trans_lt hb1))).sub
      ((((hasDerivAt_id q).const_mul phi0).add (((hasDerivAt_id q).pow 2).const_mul (slope/2)))) using 1 <;>
      first | rfl | (funext x; dsimp [F]; ring) | (simp only [Pi.sub_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  have hcont : ContinuousOn F (Icc a b) := fun q hq => (hFd q hq).continuousAt.continuousWithinAt
  have hFx : F xh=0 := by dsimp [F]; rw [hjoin]; ring
  intro q hq
  have hpos : 0≤F q := by
    by_cases hqx : q≤xh
    · have hm : AntitoneOn F (Icc q xh) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc q xh)
          (hcont.mono (Icc_subset_Icc hq.1 hx.2))
          (fun r hr => (hFd r ⟨hq.1.trans (interior_subset hr).1,(interior_subset hr).2.trans hx.2⟩).differentiableAt.differentiableWithinAt)
        intro r hr
        have hrr := interior_subset hr
        rw [(hFd r ⟨hq.1.trans hrr.1,hrr.2.trans hx.2⟩).deriv]
        have hh := hcapSlope r ⟨hq.1.trans hrr.1,hrr.2.trans hx.2⟩ xh hx hrr.2
        rw [hscore] at hh
        linarith only [hh]
      simpa only [hFx] using hm ⟨le_rfl,hqx⟩ ⟨hqx,le_rfl⟩ hqx
    · have hxq := le_of_not_ge hqx
      have hm : MonotoneOn F (Icc xh q) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc xh q)
          (hcont.mono (Icc_subset_Icc hx.1 hq.2))
          (fun r hr => (hFd r ⟨hx.1.trans (interior_subset hr).1,(interior_subset hr).2.trans hq.2⟩).differentiableAt.differentiableWithinAt)
        intro r hr
        have hrr := interior_subset hr
        rw [(hFd r ⟨hx.1.trans hrr.1,hrr.2.trans hq.2⟩).deriv]
        have hh := hcapSlope xh hx r ⟨hx.1.trans hrr.1,hrr.2.trans hq.2⟩ hrr.1
        rw [hscore] at hh
        linarith only [hh]
      simpa only [hFx] using hm ⟨le_rfl,hxq⟩ ⟨hxq,le_rfl⟩ hxq
  dsimp [F] at hpos
  linarith only [hpos]

/-- Coarse scalar bounds suffice for the cap/head comparison throughout the
actual terminal rank interval, including the tangency point. -/
theorem head_cap_gap_on_terminal {lam S phi0 slope : ℝ}
    (hl : lam≤3/5) (hS : S ∈ Icc (0:ℝ) (3/100:ℝ)) (hs : slope≤-1/10)
    (hjoin : cap lam S (527/2000)=phi0*(527/2000)+slope*(527/2000)^2/2)
    (hscore : Variational.capScore lam S (527/2000)=phi0+slope*(527/2000)) :
    ∀ q ∈ Icc (26/100:ℝ) (28/100:ℝ),phi0*q+slope*q^2/2≤cap lam S q := by
  have hd (q : ℝ) (hq : q ∈ Icc (26/100:ℝ) (28/100:ℝ)) :
      HasDerivAt (fun r => Variational.capScore lam S r-slope*r)
        (-2*lam*S/(1-q)^3-slope) q := by
    convert! (Variational.capScore_hasDerivAt lam S q (by linarith only [hq.2])).sub
      ((hasDerivAt_id q).const_mul slope) using 1 <;> first | rfl | simp
  have hm : MonotoneOn (fun r => Variational.capScore lam S r-slope*r)
      (Icc (26/100:ℝ) (28/100:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
      (fun q hq => (hd q (interior_subset hq)).differentiableAt.differentiableWithinAt)
    intro q hq
    have hqc := interior_subset hq
    rw [(hd q hqc).deriv]
    have hden0 : 0<(1-q)^3 := pow_pos (by linarith only [hqc.2]) _
    have hden : (72/100:ℝ)^3≤(1-q)^3 := pow_le_pow_left₀ (by norm_num) (by linarith only [hqc.2]) _
    have hprod := mul_le_mul hl hS.2 hS.1 (by norm_num : (0:ℝ)≤3/5)
    have hf : 2*lam*S/(1-q)^3≤1/10 := by
      apply (div_le_iff₀ hden0).mpr
      norm_num at hden
      nlinarith only [hprod,hden]
    simp only [neg_mul,neg_div]
    linarith only [hf,hs]
  apply head_cap_gap_nonneg (by norm_num : (527/2000:ℝ) ∈ Icc (26/100:ℝ) (28/100:ℝ))
    (by norm_num : (28/100:ℝ)<1) hjoin hscore
  intro u hu v hv huv
  have hh := hm hu hv huv
  dsimp only at hh
  nlinarith only [hh]

/-- The fixed-control scalar residual gives a strict backward comparison with
an actual differentiable head stationary branch. -/
theorem head_barrier_backward_gap {lam S phi0 slope pf theta alpha a b : ℝ}
    {Y dY q : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hYd : ∀ p ∈ Ioo a b,HasDerivAt Y (dY p) p)
    (hmatch : ∀ p ∈ Icc a b,headStationaryLevel lam S phi0 slope (q p)=(1-p)^2)
    (hql : ∀ p ∈ Icc a b,q p<lam) (hs : 0<1+slope)
    (hcontrol : ∀ p ∈ Ioo a b,dY p≤highAffineControl lam S pf theta alpha Y p)
    (hcheck : ∀ p ∈ Ioo a b,
      highAffineControl lam S pf theta alpha (headStationaryBarrier lam phi0 slope q) p<
        headStationaryBarrierSlope lam phi0 slope q p)
    (hend : headStationaryBarrier lam phi0 slope q b≤Y b) :
    ∀ p ∈ Ico a b,headStationaryBarrier lam phi0 slope q p<Y p := by
  have hT : ContinuousOn (headStationaryBarrier lam phi0 slope q) (Icc a b) := by
    unfold headStationaryBarrier headSlack
    fun_prop
  have hTd (p : ℝ) (hp : p ∈ Ioo a b) :
      HasDerivAt (headStationaryBarrier lam phi0 slope q)
        (headStationaryBarrierSlope lam phi0 slope q p) p :=
    headStationaryBarrier_hasDerivAt
      (headStationary_branch_hasDerivAt hp hq hmatch (hql p ⟨hp.1.le,hp.2.le⟩) hs)
      (ne_of_lt (hql p ⟨hp.1.le,hp.2.le⟩)) hs.ne'
  have hh := backward_strict_linear_comparison (alpha:=alpha) (hY.sub hT)
    (fun p hp => (hYd p hp).sub (hTd p hp)) (fun p hp => by
      have h1 := hcontrol p hp
      have h2 := hcheck p hp
      unfold highAffineControl at h1 h2
      simp only [Pi.sub_apply]
      nlinarith only [h1,h2]) (sub_nonneg.mpr hend)
  intro p hp
  exact sub_pos.mp (hh p hp)

/-- At the head-entry mass the stationary barrier is one of the original
terminal tests, so its endpoint comparison follows from feasibility. -/
theorem headStationary_terminal_eq {lam S phi0 slope p q : ℝ}
    (hql : q<lam)
    (hjoin : cap lam S q=phi0*q+slope*q^2/2)
    (hmatch : headStationaryLevel lam S phi0 slope q=(1-p)^2) :
    terminalBound lam S p q=p*((1-p)-headSlack lam phi0 slope q) := by
  have he : quadratic lam (1-p+q)-S-cap lam S q=
      (lam-q)*((1-p)-headSlack lam phi0 slope q) := by
    rw [hjoin]
    unfold quadratic headSlack
    unfold headStationaryLevel headStationaryConstant at hmatch
    nlinarith only [hmatch]
  unfold terminalBound
  rw [he]
  have hden : lam-q≠0 := (sub_pos.mpr hql).ne'
  field_simp [hden]

/-- The strict head-barrier gap on the entire initial mass band follows from
one quadratic deficit bound, finite scalar residuals, and actual terminal
feasibility at the entry rank. The original Y is used throughout. -/
theorem head_barrier_initial_gap {lam S phi0 slope pf theta alpha a m b xh C anchor : ℝ}
    {Y dY q : ℝ → ℝ}
    (ham : a≤m) (hmb : m≤b)
    (hY : ContinuousOn Y (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hYd : ∀ p ∈ Ioo a b,HasDerivAt Y (dY p) p)
    (hmatch : ∀ p ∈ Icc a b,headStationaryLevel lam S phi0 slope (q p)=(1-p)^2)
    (hqr : ∀ p ∈ Icc a b,q p ∈ Icc (0:ℝ) xh) (hxl : xh<lam) (hs : 0<1+slope)
    (hentry : headStationaryLevel lam S phi0 slope xh=(1-b)^2)
    (hjoin : cap lam S xh=phi0*xh+slope*xh^2/2)
    (hterminal : terminalBound lam S b xh≤Y b)
    (hdeficit : ∀ p ∈ Icc a m,quadratic lam p-S-Y p≤C*(max (p-anchor) 0)^2)
    (hearly : ∀ p ∈ Icc a m,∀ r ∈ Icc (0:ℝ) xh,
      headStationaryLevel lam S phi0 slope r=(1-p)^2 →
      p*((1-p)-headSlack lam phi0 slope r)<quadratic lam p-S-C*(max (p-anchor) 0)^2)
    (hcontrol : ∀ p ∈ Ioo m b,dY p≤highAffineControl lam S pf theta alpha Y p)
    (hlate : ∀ p ∈ Ioo m b,∀ r ∈ Icc (0:ℝ) xh,
      headStationaryLevel lam S phi0 slope r=(1-p)^2 →
      -theta*(p-lam)-alpha*(quadratic lam (p-pf)-S-p*((1-p)-headSlack lam phi0 slope r))<
        1-2*p-headSlack lam phi0 slope r+p*(1-p)/(lam-r)) :
    ∀ p ∈ Ico a b,headStationaryBarrier lam phi0 slope q p<Y p := by
  have hsub : Icc m b⊆Icc a b := Icc_subset_Icc ham le_rfl
  have hb : b ∈ Icc a b := ⟨ham.trans hmb,le_rfl⟩
  have hqb : q b=xh := headStationaryLevel_injective_left
    ((hqr b hb).2.trans_lt hxl) hxl hs ((hmatch b hb).trans hentry.symm)
  have hend : headStationaryBarrier lam phi0 slope q b≤Y b := by
    unfold headStationaryBarrier
    rw [hqb,←headStationary_terminal_eq hxl hjoin hentry]
    exact hterminal
  have hback := head_barrier_backward_gap (hY.mono hsub) (hq.mono hsub)
    (fun p hp => hYd p ⟨ham.trans_lt hp.1,hp.2⟩)
    (fun p hp => hmatch p (hsub hp))
    (fun p hp => (hqr p (hsub hp)).2.trans_lt hxl) hs hcontrol (fun p hp => by
      exact hlate p hp (q p) (hqr p (hsub ⟨hp.1.le,hp.2.le⟩))
        (hmatch p (hsub ⟨hp.1.le,hp.2.le⟩))) hend
  intro p hp
  by_cases hpm : p≤m
  · have h1 := hdeficit p ⟨hp.1,hpm⟩
    have h2 := hearly p ⟨hp.1,hpm⟩ (q p) (hqr p ⟨hp.1,hp.2.le⟩)
      (hmatch p ⟨hp.1,hp.2.le⟩)
    unfold headStationaryBarrier
    linarith only [h1,h2]
  · exact hback p ⟨le_of_not_ge hpm,hp.2⟩

/-- An original terminal barrier is bounded by the completed low-rank ratio
when the shifted rank is on the line and the low primitive lies below cap. -/
theorem terminalBound_le_actual_binaryRatio {phi : ℝ → ℝ} {lam S p q : ℝ}
    (hp : 0≤p) (hql : q<lam)
    (hcap : curvePrimitive phi q≤cap lam S q)
    (hshift : curvePrimitive phi (q+1-p)=quadratic lam (q+1-p)-S) :
    terminalBound lam S p q≤p*binaryRatio phi lam p q := by
  unfold terminalBound binaryRatio
  have he : 1-p+q=q+1-p := by ring
  rw [he,hshift,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hp
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hql).le
  linarith only [hcap]

/-- A strict gap against a genuine upper envelope of the original terminal
barriers excludes every contact before the entry mass. -/
theorem terminal_contact_after_head_entry {lam S a b z q : ℝ} {Y T : ℝ → ℝ}
    (hza : a≤z) (hcontact : terminalBound lam S z q=Y z)
    (hgap : ∀ p ∈ Ico a b,T p<Y p)
    (henvelope : ∀ p ∈ Ico a b,terminalBound lam S p q≤T p) : b≤z := by
  by_contra hn
  have hz : z ∈ Ico a b := ⟨hza,lt_of_not_ge hn⟩
  have hh := (henvelope z hz).trans_lt (hgap z hz)
  exact (ne_of_lt hh) hcontact

/-- Non-circular contact exclusion for the original continuation. This theorem
uses only explicit head coefficients, the original terminal tests and a
fixed-control comparison; there is no completed curve in its hypotheses. -/
theorem original_contact_after_head_entry {lam S phi0 slope pf theta alpha b z q : ℝ}
    {Y dY : ℝ → ℝ}
    (hl : lam ∈ Icc (1/2:ℝ) (3/5:ℝ)) (hS : S ∈ Icc (0:ℝ) (3/100:ℝ))
    (hs : 0<1+slope) (hsupper : slope≤-1/10)
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ))
    (hY : ContinuousOn Y (Icc (31/40:ℝ) b))
    (hYd : ∀ p ∈ Ioo (31/40:ℝ) b,HasDerivAt Y (dY p) p)
    (hleft : (1-31/40:ℝ)^2≤headStationaryLevel lam S phi0 slope 0)
    (hentry : headStationaryLevel lam S phi0 slope (527/2000)=(1-b)^2)
    (hjoin : cap lam S (527/2000)=phi0*(527/2000)+slope*(527/2000)^2/2)
    (hscore : Variational.capScore lam S (527/2000)=phi0+slope*(527/2000))
    (hterminal : terminalBound lam S b (527/2000)≤Y b)
    (hdeficit : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),
      quadratic lam p-S-Y p≤(399/500)*(max (p-391/500) 0)^2)
    (hearly : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S phi0 slope r=(1-p)^2 →
      p*((1-p)-headSlack lam phi0 slope r)<quadratic lam p-S-(399/500)*(max (p-391/500) 0)^2)
    (hcontrol : ∀ p ∈ Ioo (807/1000:ℝ) b,dY p≤highAffineControl lam S pf theta alpha Y p)
    (hlate : ∀ p ∈ Ioo (807/1000:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S phi0 slope r=(1-p)^2 →
      -theta*(p-lam)-alpha*(quadratic lam (p-pf)-S-p*((1-p)-headSlack lam phi0 slope r))<
        1-2*p-headSlack lam phi0 slope r+p*(1-p)/(lam-r))
    (hz : (31/40:ℝ)≤z) (hq : q ∈ Icc (26/100:ℝ) (28/100:ℝ))
    (hcontact : terminalBound lam S z q=Y z) : b≤z := by
  have hxl : (527/2000:ℝ)<lam := by linarith only [hl.1]
  obtain ⟨r,K,hr,hrlip,hrd⟩ := exists_head_stationary_branch
    (by norm_num : (0:ℝ)≤527/2000) hxl hs (by norm_num : (0:ℝ)≤31/40)
    (by linarith only [hb.1] : (31/40:ℝ)≤b) (by linarith only [hb.2] : b≤1)
    hleft hentry.le
  have hgap := head_barrier_initial_gap (a:=31/40) (m:=807/1000)
    (by norm_num) (by linarith only [hb.1]) hY hrlip.continuousOn hYd
    (fun p hp => (hr p hp).2) (fun p hp => (hr p hp).1) hxl hs hentry hjoin hterminal
    hdeficit hearly hcontrol hlate
  have hcap := head_cap_gap_on_terminal hl.2 hS hsupper hjoin hscore q hq
  apply terminal_contact_after_head_entry hz hcontact hgap
  intro p hp
  exact terminalBound_le_head_scalar (by linarith only [hp.1])
    (by linarith only [hq.2,hl.1]) hs.le hcap (hr p ⟨hp.1,hp.2.le⟩).2

end OptimalG
