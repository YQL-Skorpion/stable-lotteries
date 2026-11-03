import OptimalG.Certificates.ReferenceCurveMembership
import OptimalG.Certificates.IntegerRounded

/-! Exact endpoint boxes are linked to the actual C¹ reference curves and
their proved ODE error bounds. The polynomial endpoint itself is rational. -/
namespace OptimalG.Certificates
open Set
namespace IntegerInterval

def centerRadiusCheck (s : ℕ) (center radius : ℚ) (out : IntegerInterval) : Bool :=
  decide (0≤radius ∧ (out.lo:ℚ)≤(s:ℚ)*(center-radius) ∧
    (s:ℚ)*(center+radius)≤(out.hi:ℚ))

theorem centerRadiusCheck_sound {s : ℕ} {center radius : ℚ} {out : IntegerInterval}
    (hc : centerRadiusCheck s center radius out=true) {x : ℝ}
    (hx : |x-(center:ℝ)|≤(radius:ℝ)) : out.Contains s x := by
  have hh : 0≤radius ∧ (out.lo:ℚ)≤(s:ℚ)*(center-radius) ∧
      (s:ℚ)*(center+radius)≤(out.hi:ℚ) := of_decide_eq_true hc
  have hl : (out.lo:ℝ)≤(s:ℝ)*((center:ℝ)-radius) := by exact_mod_cast hh.2.1
  have hu : (s:ℝ)*((center:ℝ)+radius)≤(out.hi:ℝ) := by exact_mod_cast hh.2.2
  have ha := abs_le.mp hx
  have hs : (0:ℝ)≤s := Nat.cast_nonneg _
  constructor
  · exact hl.trans (mul_le_mul_of_nonneg_left (by linarith only [ha.1]) hs)
  · exact (mul_le_mul_of_nonneg_left (by linarith only [ha.2]) hs).trans hu

end IntegerInterval

theorem trajectoryCheck_head_primitive {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S (p::ps)=true) :
    cubicPrimitive L S (p::ps) p.lo=(p.f0:ℝ) := by
  have hp : 0<p.length := of_decide_eq_true (trajectoryCheck_head hc)
  have hq : p.lo≤p.hi := by dsimp [CubicPiece.length] at hp; linarith
  have hq' : (p.lo:ℝ)≤p.hi := by exact_mod_cast hq
  simp only [cubicPrimitive,if_pos hq',sub_self,CubicPiece.primitive]
  ring

theorem trajectoryCheck_member_endpoint {L S : ℚ} {p : CubicPiece} {ps : List CubicPiece}
    (hc : trajectoryCheck L S ps=true) (hp : p∈ps) (hlen : p.lo<p.hi) :
    cubicPrimitive L S ps p.hi=(p.primitiveQ p.length:ℝ) := by
  have hcont : Continuous (cubicPrimitive L S ps) :=
    continuous_iff_continuousAt.mpr (fun t=>(trajectoryCheck_hasDerivAt L S ps hc t).continuousAt)
  have h := cubicLookupCheck_closed_values (trajectoryCheck_lookup hc hp) hlen
    L S (trajectoryCheck_continuousScore L S ps hc) hcont
    (r:=(p.hi:ℝ)) ⟨by exact_mod_cast hlen.le,le_rfl⟩
  simpa only [CubicPiece.primitiveQ_cast,CubicPiece.length,Rat.cast_sub] using h.2

theorem checked_trajectory_endpoint {s : ℕ} {L S radius : ℚ}
    {p : CubicPiece} {ps : List CubicPiece} {out : IntegerInterval} {X : ℝ}
    (hc : trajectoryCheck L S ps=true) (hp : p∈ps) (hlen : p.lo<p.hi)
    (hbox : IntegerInterval.centerRadiusCheck s (p.primitiveQ p.length) radius out=true)
    (herror : |X-cubicPrimitive L S ps p.hi|≤(radius:ℝ)) : out.Contains s X := by
  apply IntegerInterval.centerRadiusCheck_sound hbox
  rwa [trajectoryCheck_member_endpoint hc hp hlen] at herror

end OptimalG.Certificates
