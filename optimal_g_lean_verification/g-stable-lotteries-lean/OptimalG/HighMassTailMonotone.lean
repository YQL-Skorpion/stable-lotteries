import OptimalG.VariationalRecovery
import OptimalG.MixedTailMonotonicity
import OptimalG.Certificates.TailMonotonicityBounds

namespace OptimalG
open Set Variational Certificates
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem highMass_tail_monotone {p q S Y H : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (227179/10000000:ℝ)≤S)
    (hp : p∈Icc (41/50:ℝ) (37/40)) (hq : q∈Icc (0:ℝ) lam)
    (hY : Y∈Icc (8793/100000:ℝ) (221/2500))
    (hH : H∈Icc (-3589/10000:ℝ) (-1757/5000))
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (htail : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore (539/625) Y H z)
    (hcap : curvePrimitive phi p≤quadratic lam p-S)
    (hbinary : q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam)
    {z : ℝ} (hz : z∈Icc (7/8:ℝ) 1) (hpz : p≤z) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  apply h.mixed_tail_of_derivative_numerator (R:=TailMonotonicity.primitiveCap p)
    hL hp hq (by norm_num) hline htail ?_ ?_ hbinary hz hpz
  · have hmul := mul_le_mul_of_nonneg_right hL.2 (show 0≤p by linarith only [hp.1])
    unfold TailMonotonicity.primitiveCap quadratic at *
    linarith only [hmul,hS,hcap]
  · intro t ht
    exact TailMonotonicity.numerator_nonneg hp hY hH ht

end VerifierCurve
end OptimalG
