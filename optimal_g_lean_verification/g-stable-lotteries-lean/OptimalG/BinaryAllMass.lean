import OptimalG.BinaryOriginalRange
import OptimalG.BinaryLateAssembly
import OptimalG.BinaryContinuationInputs

/-! C.3 assembly for every mass and every split. The numerical inputs below
are explicit scalar residuals. Branch construction, global maximization,
integral estimates, and coverage of the mass interval are proved by the
imported analytic lemmas. -/
namespace OptimalG
open Set Variational

/-- Scalar tests for the head and rational stationary bands. Each variable
ranges over a displayed compact interval; no unknown primitive or binary
inequality occurs in this certificate interface. -/
structure BinaryStationaryIntervals (lam S phi0 slope z T H : ℝ) : Prop where
  head_left : (1-31/40:ℝ)^2≤headStationaryLevel lam S phi0 slope 0
  cap_end : stationaryLevel lam S (1459/5000)≤(7/80:ℝ)^2
  head_shift : ∀ p ∈ Icc (31/40:ℝ) (17/20:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
    headStationaryLevel lam S phi0 slope r=(1-p)^2 → 7189/20000≤r+1-p
  head_zero : ∀ p ∈ Icc (31/40:ℝ) (17/20:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
    headStationaryLevel lam S phi0 slope r=(1-p)^2 →
    phi0*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-headSlack lam phi0 slope r)
  head_early : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
    headStationaryLevel lam S phi0 slope r=(1-p)^2 →
    p*((1-p)-headSlack lam phi0 slope r)<
      quadratic lam p-S-(399/500)*(max (p-391/500) 0)^2
  head_late : ∀ p ∈ Ioo (807/1000:ℝ) (17/20:ℝ),∀ r ∈ Icc (0:ℝ) (527/2000:ℝ),
    headStationaryLevel lam S phi0 slope r=(1-p)^2 →
    -capDiagonalTheta lam S (29/100) (1459/5000)*(p-lam)-
      capDiagonalAlpha lam S (29/100) (1459/5000)*
        (quadratic lam (p-29/100)-S-p*((1-p)-headSlack lam phi0 slope r))<
      1-2*p-headSlack lam phi0 slope r+p*(1-p)/(lam-r)
  cap_shift : ∀ p ∈ Icc (849/1000:ℝ) (73/80:ℝ),∀ r ∈ Icc (527/2000:ℝ) (1459/5000:ℝ),
    stationaryLevel lam S r=(1-p)^2 → 7189/20000≤r+1-p
  cap_zero : ∀ p ∈ Icc (849/1000:ℝ) (73/80:ℝ),∀ r ∈ Icc (527/2000:ℝ) (1459/5000:ℝ),
    stationaryLevel lam S r=(1-p)^2 →
    phi0*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-capSlack lam S r)
  cap_curvature : ∀ p ∈ Ioo z (73/80:ℝ),∀ r ∈ Icc (527/2000:ℝ) (1459/5000:ℝ),
    stationaryLevel lam S r=(1-p)^2 → stationaryBarrierCurvature lam S p r≤tailSlope z T H p

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

/-- Every positive mass below one satisfies the normalized binary test.
The contact/entry identities are actual geometric data; all remaining
inequalities about displayed scalar profiles are grouped in the three
numerical interfaces. -/
theorem binary_all_mass (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    {Y dY : ℝ→ℝ} {b z qs T H B C : ℝ} {n : ℕ}
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ))
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ)) (hbz : b≤z) (hz : z≤7/8)
    (hqs : qs ∈ Icc (527/2000:ℝ) (691/2500:ℝ))
    (hentry : headStationaryLevel lam S (phi 0) slope (527/2000)=(1-b)^2)
    (hcontact : stationaryLevel lam S qs=(1-z)^2)
    (hcontactValue : curvePrimitive phi z=z*((1-z)-capSlack lam S qs))
    (hcontactSlope : phi z=1-2*z-capSlack lam S qs+z*(1-z)/(lam-qs))
    (hactual : ∀ p ∈ Icc (31/40:ℝ) z,curvePrimitive phi p=Y p)
    (htailScore : ∀ p ∈ Icc z 1,phi p=tailScore z T H p)
    (htailPrimitive : ∀ p ∈ Icc z 1,curvePrimitive phi p=tailPrimitive z T H p)
    (hY : ContinuousOn Y (Icc (31/40:ℝ) z))
    (hYd : ∀ p ∈ Ioo (31/40:ℝ) z,HasDerivAt Y (dY p) p)
    (hterminal : ∀ p ∈ Icc (21/25:ℝ) (7/8:ℝ),∀ q ∈ Icc (26/100:ℝ) (28/100:ℝ),
      terminalBound lam S p q≤Y p)
    (hdeficit : ∀ p ∈ Icc (31/40:ℝ) (807/1000:ℝ),
      quadratic lam p-S-Y p≤(399/500)*(max (p-391/500) 0)^2)
    (hcontrol : ∀ p ∈ Ioo (807/1000:ℝ) b,dY p≤highAffineControl lam S (29/100)
      (capDiagonalTheta lam S (29/100) (1459/5000))
      (capDiagonalAlpha lam S (29/100) (1459/5000)) Y p)
    (hs : 0<capSlack lam S c)
    (harea : binarySlackArea phi lam S (348541/1000000)≤87/1000000000)
    (hscore : scoreDefect phi lam (348541/1000000)≤24/100000)
    (hA : tailBackwardSlope z T H/2-1≤B)
    (hdecay : tailBackwardSlope z T H/2-1≤tailBackwardCurvature z T H/3)
    (haffine : tailBackwardSlope z T H/2-1-(tailBackwardCurvature z T H/3)*(7/80)≤B-C*(7/80))
    (small : BinarySmallIntervals lam S (phi 0) slope (527/2000) c)
    (stationary : BinaryStationaryIntervals lam S (phi 0) slope z T H)
    (late : BinaryLateIntervals lam S (phi 0) slope c (348541/1000000)
      (87/1000000000) (24/100000) B C n) :
    ∀ p ∈ Ioo (0:ℝ) 1,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hsmall := g.binary_small_central h hc small harea hscore
  have hjoin : cap lam S (527/2000)=(phi 0)*(527/2000)+slope*(527/2000)^2/2 := by
    rw [←g.cap_primitive (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩]
    exact h.affine_head_primitive g.head ⟨by norm_num,le_rfl⟩
  have hjoinScore := g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  rw [g.head (527/2000) ⟨by norm_num,le_rfl⟩] at hjoinScore
  have hcapEntry : stationaryLevel lam S (527/2000)=(1-b)^2 :=
    (headStationaryLevel_eq_cap hjoin hjoinScore.symm).symm.trans hentry
  have hhead := g.binary_head_range h hc hb
    (hY.mono (Icc_subset_Icc le_rfl hbz))
    (fun p hp => hYd p ⟨hp.1,hp.2.trans_le hbz⟩)
    (fun p hp => hactual p ⟨hp.1,hp.2.trans hbz⟩) stationary.head_left hentry
    (hterminal b ⟨by linarith only [hb.1],by linarith only [hb.2]⟩ (527/2000) (by norm_num))
    hdeficit stationary.head_early hcontrol
    (fun p hp => stationary.head_late p ⟨hp.1,hp.2.trans_le hb.2⟩)
    (fun p hp => stationary.head_shift p ⟨hp.1,hp.2.trans hb.2⟩)
    (fun p hp => stationary.head_zero p ⟨hp.1,hp.2.trans hb.2⟩)
  have hmiddle := g.binary_entry_to_contact h hc hS hb hbz hz hqs hcapEntry hcontact hterminal
    (fun p hp => hactual p ⟨by linarith only [hp.1,hb.1],hp.2⟩)
    (fun p hp r hr => stationary.cap_shift p
      ⟨hb.1.trans hp.1,by linarith only [hp.2,hz]⟩ r
      ⟨hr.1,by linarith only [hr.2,hqs.2]⟩)
    (fun p hp r hr => stationary.cap_zero p
      ⟨hb.1.trans hp.1,by linarith only [hp.2,hz]⟩ r
      ⟨hr.1,by linarith only [hr.2,hqs.2]⟩)
  have hafter := g.binary_after_contact h hc hS ⟨hb.1.trans hbz,hz⟩ hqs hcontact
    hcontactValue hcontactSlope htailScore stationary.cap_end
    (fun p hp r hr => stationary.cap_shift p ⟨(hb.1.trans hbz).trans hp.1,hp.2⟩ r
      ⟨hqs.1.trans hr.1,hr.2⟩)
    (fun p hp r hr => stationary.cap_zero p ⟨(hb.1.trans hbz).trans hp.1,hp.2⟩ r
      ⟨hqs.1.trans hr.1,hr.2⟩)
    (fun p hp r hr => stationary.cap_curvature p hp r ⟨hqs.1.trans hr.1,hr.2⟩)
  have hlate := g.binary_late_all h hc hs
    ⟨by linarith only [g.contact_mem.2],by norm_num⟩ harea hscore
    (by linarith only [hz] : z<1)
    (fun p hp => htailPrimitive p ⟨by linarith only [hp.1,hz],hp.2.le⟩) hA hdecay haffine late
  intro p hp
  by_cases hps : p≤31/40
  · exact hsmall p ⟨hp.1,hps⟩
  · by_cases hpb : p≤b
    · exact hhead p ⟨le_of_not_ge hps,hpb⟩
    · by_cases hpz : p≤z
      · exact hmiddle p ⟨le_of_not_ge hpb,hpz⟩
      · by_cases hpr : p≤73/80
        · exact hafter p ⟨le_of_not_ge hpz,hpr⟩
        · exact hlate p ⟨le_of_not_ge hpr,hp.2⟩

/-- The same all-mass conclusion with trajectory comparison hypotheses
eliminated using the actual variational ODE and its supported cap control.
The remaining parabola residual is an explicit numerical control test. -/
theorem binary_all_mass_of_continuation (h : VerifierCurve phi lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    {Y : ℝ→ℝ} {d : LowRankData} {b z qs T H B C : ℝ} {n : ℕ}
    (hd : Admissible lam d) (hYsol : IsContinuation lam d Y) (hSvalue : d.S=S)
    (hline : ∀ r ∈ Icc zStart (391/500:ℝ),continuationScore lam d Y r=lam-r)
    (hparabola : ∀ r ∈ Ico (391/500:ℝ) (807/1000:ℝ),∀ v ∈ controlFeatureSupport d,
      lam-r-2*(399/500)*(r-391/500)≤
        -featureTheta lam d v*(r-lam)-featureAlpha lam d v*
          (quadratic lam (r-v.1.1)-d.S-(quadratic lam r-d.S-(399/500)*(r-391/500)^2)))
    (hsupport : ((1459/5000:ℝ),capScore lam d.S (1459/5000))∈rankScoreSupport d.phi)
    (hR : primitive lam d (29/100)=cap lam d.S (29/100))
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ))
    (hb : b ∈ Icc (849/1000:ℝ) (17/20:ℝ)) (hbz : b≤z) (hz : z≤7/8)
    (hqs : qs ∈ Icc (527/2000:ℝ) (691/2500:ℝ))
    (hentry : headStationaryLevel lam S (phi 0) slope (527/2000)=(1-b)^2)
    (hcontact : stationaryLevel lam S qs=(1-z)^2)
    (hcontactValue : curvePrimitive phi z=z*((1-z)-capSlack lam S qs))
    (hcontactSlope : phi z=1-2*z-capSlack lam S qs+z*(1-z)/(lam-qs))
    (hactual : ∀ p ∈ Icc (31/40:ℝ) z,curvePrimitive phi p=Y p)
    (htailScore : ∀ p ∈ Icc z 1,phi p=tailScore z T H p)
    (htailPrimitive : ∀ p ∈ Icc z 1,curvePrimitive phi p=tailPrimitive z T H p)
    (hterminal : ∀ p ∈ Icc (21/25:ℝ) (7/8:ℝ),∀ q ∈ Icc (26/100:ℝ) (28/100:ℝ),
      terminalBound lam S p q≤Y p)
    (hs : 0<capSlack lam S c)
    (harea : binarySlackArea phi lam S (348541/1000000)≤87/1000000000)
    (hscore : scoreDefect phi lam (348541/1000000)≤24/100000)
    (hA : tailBackwardSlope z T H/2-1≤B)
    (hdecay : tailBackwardSlope z T H/2-1≤tailBackwardCurvature z T H/3)
    (haffine : tailBackwardSlope z T H/2-1-(tailBackwardCurvature z T H/3)*(7/80)≤B-C*(7/80))
    (small : BinarySmallIntervals lam S (phi 0) slope (527/2000) c)
    (stationary : BinaryStationaryIntervals lam S (phi 0) slope z T H)
    (late : BinaryLateIntervals lam S (phi 0) slope c (348541/1000000)
      (87/1000000000) (24/100000) B C n) :
    ∀ p ∈ Ioo (0:ℝ) 1,∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  subst S
  have hinputs := continuation_binary_head_inputs hd hYsol hline hparabola hsupport hR
  have hsubset : Icc (31/40:ℝ) z⊆Icc zStart zEnd := by
    apply Icc_subset_Icc
    · norm_num [zStart]
    · norm_num [zEnd]
      exact hz
  have hYcont := (continuation_continuous hYsol).mono hsubset
  have hYderiv : ∀ p ∈ Ioo (31/40:ℝ) z,
      HasDerivAt Y (vectorField lam d p (Y p)) p := by
    intro p hp
    apply (hYsol.2 p (hsubset ⟨hp.1.le,hp.2.le⟩)).hasDerivAt
    apply Icc_mem_nhds
    · norm_num [zStart]
      exact hp.1
    · norm_num [zEnd]
      exact hp.2.trans_le hz
  exact g.binary_all_mass h hc hS hb hbz hz hqs hentry hcontact
    hcontactValue hcontactSlope hactual htailScore htailPrimitive hYcont hYderiv hterminal
    hinputs.1 (fun p hp => (hinputs.2 p ⟨hp.1.le,hp.2.le.trans hb.2⟩).2)
    hs harea hscore hA hdecay haffine small stationary late

end BinaryCurveGeometry
end OptimalG
