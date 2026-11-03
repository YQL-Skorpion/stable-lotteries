import OptimalG.HighMassGeometry
import OptimalG.TailControl
import OptimalG.VariationalRecovery

namespace OptimalG
open Set Variational

/-- The terminal derivative estimate for the last three percent of ranks.
The positive curvature term is retained before bounding the remaining linear
term, so there is no interval-arithmetic loss at the endpoint. -/
theorem small_split_tail_derivative_nonneg {lam v g t : ℝ}
    (hL : (22493/40000:ℝ)≤lam) (hv : v≤321/50) (hg : (1077/100:ℝ)≤g)
    (ht : t∈Icc (0:ℝ) (3/100)) :
    0≤1-v+2*g*t+(247/50)*(lam+3/5-v*t+g*t^2) := by
  have ht0 : 0≤t := ht.1
  have hvp := mul_nonneg (sub_nonneg.mpr hv)
    (show 0≤1+(247/50:ℝ)*t by positivity)
  have hgp := mul_nonneg (sub_nonneg.mpr hg)
    (show 0≤2*t+(247/50:ℝ)*t^2 by positivity)
  have hs := sq_nonneg t
  nlinarith only [hvp,hgp,hs,hL,ht.2]

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem highMass_beta_lower {p S : ℝ}
    (hp : p∈Ico (13/20:ℝ) 1) (hL : lam≤56233/100000)
    (hS : (227179/10000000:ℝ)≤S)
    (hcap : curvePrimitive phi p≤quadratic lam p-S) :
    (247/50:ℝ)≤p/curvePrimitive phi p := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hJ := h.primitive_pos ⟨hp0,hp.2⟩
  rw [le_div_iff₀ hJ]
  have hm := mul_le_mul_of_nonneg_right hL hp0.le
  have hs := sq_nonneg (p-13/20)
  unfold quadratic at hcap
  nlinarith only [hcap,hm,hS,hp.1,hs]

end VerifierCurve
end OptimalG
