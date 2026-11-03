import OptimalG.NearEndpointTailBounds
import OptimalG.MixedTailDerivativeCriterion

namespace OptimalG
open Set Variational
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The genuinely tight binary endpoint is handled analytically for small
splits, leaving the remaining finite tail checks a positive margin. -/
theorem highMass_small_split_near_endpoint {p q S a Y H : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (227179/10000000:ℝ)≤S)
    (hp : p∈Icc (13/20:ℝ) (37/40)) (hq : q∈Icc (0:ℝ) (1/20))
    (ha : a≠1) (hv : tailBackwardSlope a Y H≤321/50)
    (hg : (1077/100:ℝ)≤tailBackwardCurvature a Y H)
    (hline : phi (2/5)=lam-2/5)
    (htail : ∀ z∈Icc (7/8:ℝ) 1,phi z=tailScore a Y H z)
    (hcap : curvePrimitive phi p≤quadratic lam p-S)
    (hbinary : q+(p/curvePrimitive phi p)*packingDelta phi p q≤lam)
    {z : ℝ} (hz : z∈Icc (97/100:ℝ) 1) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have hp0 : 0<p := by linarith only [hp.1]
  have hp1 : p<1 := by linarith only [hp.2]
  have hbeta := h.highMass_beta_lower ⟨hp.1,hp1⟩ hL.2 hS hcap
  have hb0 : 0≤p/curvePrimitive phi p := by linarith only [hbeta]
  apply h.mixed_tail_of_nonnegative_derivative (cut:=97/100) (a:=a) (Y:=Y) (H:=H) ⟨hp0,hp1⟩
    ⟨hq.1,by linarith only [hq.2,hp.1]⟩ ?_ ?_ hbinary z
    ⟨max_le (by linarith only [hz.1,hp.2]) hz.1,hz.2⟩
  · intro r hr
    exact htail r ⟨by linarith only [hr.1],hr.2⟩
  · intro r hr
    have hr97 : (97/100:ℝ)≤r := (le_max_right _ _).trans hr.1
    have hrp : p≤r := (le_max_left _ _).trans hr.1
    have hrr : r-p+q∈Icc (0:ℝ) (2/5) := by
      constructor <;> linarith only [hrp,hr.2,hq.1,hq.2,hp.1]
    have hdelay := h.decreasing.antitoneOn
      ⟨hrr.1,by linarith only [hrr.2]⟩ (by constructor <;> norm_num) hrr.2
    rw [hline] at hdelay
    have hm1 := mul_le_mul_of_nonneg_left hdelay hb0
    have ht := htail r ⟨by linarith only [hr97],hr.2⟩
    have hceil := h.ceiling r ⟨by linarith only [hr97],hr.2⟩
    have hcoef : 0≤lam-2/5-tailScore a Y H r := by
      rw [←ht]
      linarith only [hceil,hr97]
    have hm2 := mul_le_mul_of_nonneg_right hbeta hcoef
    have htau : 1-r∈Icc (0:ℝ) (3/100) := by
      constructor <;> linarith only [hr97,hr.2]
    have hnum := small_split_tail_derivative_nonneg hL.1 hv hg htau
    have hnum' : 0≤1+(247/50)*(lam-2/5-tailScore a Y H r)+tailSlope a Y H r := by
      rw [tailScore_backward a Y H r ha,tailSlope_backward a Y H r ha]
      convert hnum using 1 <;> ring
    rw [ht]
    nlinarith only [hm1,hm2,hnum']

end VerifierCurve
end OptimalG
