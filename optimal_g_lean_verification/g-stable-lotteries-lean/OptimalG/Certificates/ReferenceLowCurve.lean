import OptimalG.Certificates.TransportReference
import OptimalG.Certificates.HighAssembly
import OptimalG.Certificates.CapCubic
import OptimalG.Certificates.CubicEvaluation

/-! The reference low profile is a genuine C¹ primitive, independently of
whether that reference is itself feasible. All joins are exact rational tests. -/
namespace OptimalG.Certificates.Transport.ReferenceData
open Set

noncomputable def lowPrimitive (d : ReferenceData) : ℝ→ℝ :=
  capCubicPrimitive d.lam d.slack d.leftContact d.pieces
noncomputable def lowScore (d : ReferenceData) : ℝ→ℝ :=
  capCubicScore d.lam d.slack d.leftContact d.pieces

def lowCurveCheck (d : ReferenceData) : Bool :=
  match d.pieces with
  | [] => false
  | p::ps => trajectoryCheck d.lam d.slack (p::ps) &&
      decide (d.leftContact<1 ∧ p.lo=d.leftContact ∧
        p.a0=d.lam/2-d.lam*d.slack/(1-d.leftContact)^2 ∧
        p.f0=d.lam^2-d.lam/2+d.lam*d.leftContact/2-d.lam*d.slack/(1-d.leftContact))

theorem lowCurveCheck_joins (d : ReferenceData) (hc : d.lowCurveCheck=true) :
    (d.leftContact:ℝ)<1 ∧ trajectoryCheck d.lam d.slack d.pieces=true ∧
      cap d.lam d.slack d.leftContact=cubicPrimitive d.lam d.slack d.pieces d.leftContact ∧
      capSlope d.lam d.slack d.leftContact=cubicScore d.lam d.pieces d.leftContact := by
  cases hp : d.pieces with
  | nil => simp [lowCurveCheck,hp] at hc
  | cons p ps =>
    have hh : trajectoryCheck d.lam d.slack (p::ps)=true ∧
        (d.leftContact<1 ∧ p.lo=d.leftContact ∧
          p.a0=d.lam/2-d.lam*d.slack/(1-d.leftContact)^2 ∧
          p.f0=d.lam^2-d.lam/2+d.lam*d.leftContact/2-d.lam*d.slack/(1-d.leftContact)) := by
      simpa only [lowCurveCheck,hp,Bool.and_eq_true,decide_eq_true_eq] using hc
    have hlen : 0<p.length := of_decide_eq_true (trajectoryCheck_head hh.1)
    have horder : p.lo≤p.hi := by unfold CubicPiece.length at hlen;linarith
    have hv := cubicPrimitive_at_first d.lam d.slack p ps horder
    have hs := cubicScore_at_first d.lam p ps horder
    rw [hh.2.2.1] at hv hs
    have hval : (p.f0:ℝ)=cap d.lam d.slack d.leftContact := by
      have h := congrArg (fun q:ℚ => (q:ℝ)) hh.2.2.2.2
      simpa [cap] using h
    have hscore : (p.a0:ℝ)=capSlope d.lam d.slack d.leftContact := by
      have h := congrArg (fun q:ℚ => (q:ℝ)) hh.2.2.2.1
      simpa [capSlope] using h
    refine ⟨by exact_mod_cast hh.2.1,by simpa only [hp] using hh.1,?_,?_⟩
    · simpa only [hp] using (hv.trans hval).symm
    · simpa only [hp] using (hs.trans hscore).symm

theorem lowPrimitive_hasDerivAt (d : ReferenceData) (hc : d.lowCurveCheck=true) (r : ℝ) :
    HasDerivAt d.lowPrimitive (d.lowScore r) r := by
  obtain ⟨hcap,hcurve,hv,hs⟩ := lowCurveCheck_joins d hc
  apply hasDerivAt_glue_le_of_left (d.leftContact:ℝ)
    (cap d.lam d.slack) (cubicPrimitive d.lam d.slack d.pieces)
    (capSlope d.lam d.slack) (cubicScore d.lam d.pieces) ?_
    (trajectoryCheck_hasDerivAt d.lam d.slack d.pieces hcurve) hv hs r
  intro x hx
  exact cap_hasDerivAt d.lam d.slack x (ne_of_lt (hx.trans_lt hcap))

theorem lowScore_continuous (d : ReferenceData) (hc : d.lowCurveCheck=true) :
    Continuous d.lowScore := by
  obtain ⟨hcap,hcurve,_,hs⟩ := lowCurveCheck_joins d hc
  have hmin : Continuous (fun r:ℝ => min r (d.leftContact:ℝ)) := continuous_id.min continuous_const
  have hn : ∀ r:ℝ,(1-min r (d.leftContact:ℝ))^2≠0 := fun r =>
    pow_ne_zero _ (ne_of_gt (sub_pos.mpr ((min_le_right r _).trans_lt hcap)))
  have hp : Continuous (fun r:ℝ => capSlope d.lam d.slack (min r d.leftContact)) := by
    unfold capSlope
    exact continuous_const.sub (continuous_const.div ((continuous_const.sub hmin).pow 2) hn)
  have h := hp.if_le (trajectoryCheck_continuousScore d.lam d.slack d.pieces hcurve)
    continuous_id continuous_const (fun r hr => by
      change r=(d.leftContact:ℝ) at hr
      subst r
      simpa only [min_self] using hs)
  convert h using 1
  funext r
  by_cases hr : r≤(d.leftContact:ℝ)
  · simp only [lowScore,capCubicScore,id_eq,if_pos hr,min_eq_left hr]
  · simp only [lowScore,capCubicScore,id_eq,if_neg hr]

theorem lowPrimitive_continuous (d : ReferenceData) (hc : d.lowCurveCheck=true) :
    Continuous d.lowPrimitive :=
  continuous_iff_continuousAt.mpr (fun r => (lowPrimitive_hasDerivAt d hc r).continuousAt)

end OptimalG.Certificates.Transport.ReferenceData
