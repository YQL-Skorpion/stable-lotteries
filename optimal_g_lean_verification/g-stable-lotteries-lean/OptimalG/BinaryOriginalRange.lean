import OptimalG.BinaryRationalRange

/-! Between head entry and contact, the actual original terminal tests cover
the constructed stationary branch. Before entry, the strict head comparison
covers the same global ratio maximum. -/
namespace OptimalG
open Set Variational

namespace BinaryCurveGeometry
variable {phi : ℝ → ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

theorem binary_entry_to_contact (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi) {Y : ℝ → ℝ} {b z qs : ℝ}
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ))
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ)) (hbz : b≤z) (hz : z≤7/8)
    (hqs : qs ∈ Icc (527/2000:ℝ) (691/2500:ℝ))
    (hentry : stationaryLevel lam S (527/2000)=(1-b)^2)
    (hcontact : stationaryLevel lam S qs=(1-z)^2)
    (hterminal : ∀ p ∈ Icc (21/25:ℝ) (7/8:ℝ),∀ q ∈ Icc (26/100:ℝ) (28/100:ℝ),
      terminalBound lam S p q≤Y p)
    (hactual : ∀ p ∈ Icc b z,curvePrimitive phi p=Y p)
    (hshift : ∀ p ∈ Icc b z,∀ r ∈ Icc (527/2000:ℝ) qs,
      stationaryLevel lam S r=(1-p)^2 → 7189/20000≤r+1-p)
    (hzero : ∀ p ∈ Icc b z,∀ r ∈ Icc (527/2000:ℝ) qs,
      stationaryLevel lam S r=(1-p)^2 →
      (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-capSlack lam S r)) :
    ∀ p ∈ Icc b z,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hl : lam ∈ Icc (11/20:ℝ) (3/5:ℝ) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hqsl : qs<lam := by linarith only [hqs.2,g.lambda_mem.1]
  obtain ⟨r,hr,hrlip,hrd⟩ := exists_rational_stationary_branch hqs.1
    (by linarith only [hqs.2] : qs<1) hqsl (by linarith only [hb.1] : 0≤b)
    hbz (by linarith only [hz] : z≤1) (by norm_num : (0:ℝ)<2/5)
    (fun r hr => capStationarySlope_lower hl hS (by linarith only [hr.2,hqs.2]))
    hentry.ge hcontact.le
  intro p hp
  have hpr := (hr p hp).1
  have hlevel := (hr p hp).2
  have hrc : r p≤c := by linarith only [hpr.2,hqs.2,g.contact_mem.1]
  have hrl : r p<lam := hpr.2.trans_lt hqsl
  have hrshift := hshift p hp (r p) hpr hlevel
  have hsmem : r p+1-p ∈ Icc (7189/20000:ℝ) (31/40:ℝ) :=
    ⟨hrshift,by linarith only [hpr.2,hqs.2,hp.1,hb.1]⟩
  have hroot := rationalStationary_actual_root (g.cap_primitive (r p) ⟨hpr.1,hrc⟩)
    (g.cap_score (r p) ⟨hpr.1,hrc⟩) (g.line_primitive _ hsmem) (g.line_score _ hsmem) hlevel
  have hratio : binaryRatio phi lam p (r p)=(1-p)-capSlack lam S (r p) := by
    rw [h.binaryRatio_eq_deficit hrl hroot (g.line_score _ hsmem),g.cap_score (r p) ⟨hpr.1,hrc⟩]
    rfl
  have hterminalP := hterminal p ⟨by linarith only [hp.1,hb.1],hp.2.trans hz⟩
    (r p) ⟨by linarith only [hpr.1],by linarith only [hpr.2,hqs.2]⟩
  have hte : terminalBound lam S p (r p)=p*binaryRatio phi lam p (r p) := by
    unfold terminalBound binaryRatio
    have he : 1-p+r p=r p+1-p := by ring
    rw [he,g.cap_primitive (r p) ⟨hpr.1,hrc⟩,g.line_primitive _ hsmem]
    ring
  rw [hte,hratio,←hactual p hp] at hterminalP
  exact g.binary_of_stationary_value h hc
    ⟨by linarith only [hp.1,hb.1],by linarith only [hp.2,hz]⟩
    ⟨by linarith only [hpr.1],hrl⟩ hrshift hroot hratio
    (hzero p hp (r p) hpr hlevel) hterminalP

/-- A head branch built from the scalar endpoint equation controls the whole
initial mass band once its proved original-continuation gap is supplied. -/
theorem binary_head_from_gap (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi) {Y r : ℝ → ℝ} {b : ℝ}
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ))
    (hactual : ∀ p ∈ Icc (31/40:ℝ) b,curvePrimitive phi p=Y p)
    (hr : ∀ p ∈ Icc (31/40:ℝ) b,r p ∈ Icc (0:ℝ) (527/2000:ℝ))
    (hmatch : ∀ p ∈ Icc (31/40:ℝ) b,headStationaryLevel lam S (phi 0) slope (r p)=(1-p)^2)
    (hshift : ∀ p ∈ Icc (31/40:ℝ) b,∀ q ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope q=(1-p)^2 → 7189/20000≤q+1-p)
    (hzero : ∀ p ∈ Icc (31/40:ℝ) b,∀ q ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope q=(1-p)^2 →
      (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-headSlack lam (phi 0) slope q))
    (hgap : ∀ p ∈ Icc (31/40:ℝ) b,headStationaryBarrier lam (phi 0) slope r p≤Y p) :
    ∀ p ∈ Icc (31/40:ℝ) b,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  intro p hp
  have hrp := hr p hp
  have hlevel := hmatch p hp
  have hpp : p ∈ Icc (31/40:ℝ) (17/20:ℝ) := ⟨hp.1,hp.2.trans hb.2⟩
  have hrshift := hshift p hp (r p) hrp hlevel
  have hrl : r p<lam := by linarith only [hrp.2,g.lambda_mem.1]
  have hroot := g.head_root h hpp hrp hrshift hlevel
  have hratio : binaryRatio phi lam p (r p)=(1-p)-headSlack lam (phi 0) slope (r p) := by
    rw [h.binaryRatio_eq_deficit hrl hroot
      (g.line_score _ ⟨hrshift,by linarith only [hrp.2,hp.1]⟩),g.head _ hrp]
    rfl
  have hvalue := hgap p hp
  change p*((1-p)-headSlack lam (phi 0) slope (r p))≤Y p at hvalue
  rw [←hactual p hp] at hvalue
  exact g.binary_of_stationary_value h hc ⟨hp.1,by linarith only [hp.2,hb.2]⟩
    ⟨hrp.1,hrl⟩ hrshift hroot hratio (hzero p hp (r p) hrp hlevel) hvalue

/-- All head-band binary tests are proved from a constructed branch and the
original continuation comparison; no maximizing-rank assumption is required. -/
theorem binary_head_range (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi) {Y dY : ℝ → ℝ} {b pf theta alpha : ℝ}
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ))
    (hY : ContinuousOn Y (Icc (31/40:ℝ) b))
    (hYd : ∀ p ∈ Ioo (31/40:ℝ) b,HasDerivAt Y (dY p) p)
    (hactual : ∀ p ∈ Icc (31/40:ℝ) b,curvePrimitive phi p=Y p)
    (hleft : (1-31/40:ℝ)^2≤headStationaryLevel lam S (phi 0) slope 0)
    (hentry : headStationaryLevel lam S (phi 0) slope (527/2000)=(1-b)^2)
    (hterminal : terminalBound lam S b (527/2000)≤Y b)
    (hdeficit : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),
      quadratic lam p-S-Y p≤(399/500)*(max (p-391/500) 0)^2)
    (hearly : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      p*((1-p)-headSlack lam (phi 0) slope r)<quadratic lam p-S-(399/500)*(max (p-391/500) 0)^2)
    (hcontrol : ∀ p ∈ Ioo (807/1000:ℝ) b,dY p≤highAffineControl lam S pf theta alpha Y p)
    (hlate : ∀ p ∈ Ioo (807/1000:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      -theta*(p-lam)-alpha*(quadratic lam (p-pf)-S-p*((1-p)-headSlack lam (phi 0) slope r))<
        1-2*p-headSlack lam (phi 0) slope r+p*(1-p)/(lam-r))
    (hshift : ∀ p ∈ Icc (31/40:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 → 7189/20000≤r+1-p)
    (hzero : ∀ p ∈ Icc (31/40:ℝ) b,∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
      headStationaryLevel lam S (phi 0) slope r=(1-p)^2 →
      (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-headSlack lam (phi 0) slope r)) :
    ∀ p ∈ Icc (31/40:ℝ) b,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hxl : (527/2000:ℝ)<lam := by linarith only [g.lambda_mem.1]
  have hs : 0<1+slope := by linarith only [g.head_slope]
  have hab : (31/40:ℝ)≤b := by linarith only [hb.1]
  obtain ⟨r,K,hr,hrlip,hrd⟩ := exists_head_stationary_branch
    (by norm_num : (0:ℝ)≤527/2000) hxl hs (by norm_num : (0:ℝ)≤31/40) hab
    (by linarith only [hb.2] : b≤1) hleft hentry.le
  have hjoin : cap lam S (527/2000)=(phi 0)*(527/2000)+slope*(527/2000)^2/2 := by
    rw [←g.cap_primitive (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩]
    exact h.affine_head_primitive g.head ⟨by norm_num,le_rfl⟩
  have hgap := head_barrier_initial_gap (a:=31/40) (m:=807/1000)
    (by norm_num) (by linarith only [hb.1]) hY hrlip.continuousOn hYd
    (fun p hp => (hr p hp).2) (fun p hp => (hr p hp).1) hxl hs hentry hjoin hterminal
    hdeficit hearly hcontrol hlate
  have hrb : r b=527/2000 := headStationaryLevel_injective_left
    ((hr b ⟨hab,le_rfl⟩).1.2.trans_lt hxl) hxl hs
    ((hr b ⟨hab,le_rfl⟩).2.trans hentry.symm)
  have hend : headStationaryBarrier lam (phi 0) slope r b≤Y b := by
    unfold headStationaryBarrier
    rw [hrb,←headStationary_terminal_eq hxl hjoin hentry]
    exact hterminal
  apply g.binary_head_from_gap h hc hb hactual (fun p hp => (hr p hp).1)
    (fun p hp => (hr p hp).2) hshift hzero
  intro p hp
  by_cases hpb : p=b
  · simpa only [hpb] using hend
  · exact (hgap p ⟨hp.1,lt_of_le_of_ne hp.2 hpb⟩).le

end BinaryCurveGeometry
end OptimalG
