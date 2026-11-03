import OptimalG.ConcaveGlue
import OptimalG.CompletedVerifierCurve

/-! The high-rank part of the completed curve remains concave when the
polynomial tail makes the certified downward derivative jump. -/
namespace OptimalG
open Set

theorem completedScore_high_concave {lam x J f z Y H slopeLeft : ℝ} {psi : ℝ → ℝ}
    (hx : x ≠ 0) (hxl : x ≤ lam) (hlz : lam ≤ z) (hz : z < 1)
    (hxjoin : psi x=f) (hzjoin : psi z=H)
    (hpsi : ConcaveOn ℝ (Icc lam z) psi)
    (hpsiD : HasDerivWithinAt psi slopeLeft (Icc lam z) z)
    (htwo : tailTwo z Y H ≤ 0) (hjump : tailOne z Y H/(1-z) ≤ slopeLeft) :
    ConcaveOn ℝ (Icc lam 1) (completedScore x J f z Y H psi) := by
  have htailD : HasDerivWithinAt (tailScore z Y H) (tailOne z Y H/(1-z)) (Icc z 1) z := by
    simpa only [tailSlope,tailCoord,sub_self,zero_div,mul_zero,add_zero] using
      (tailScore_hasDerivAt z Y H z).hasDerivWithinAt (s := Icc z 1)
  have hjoin : psi z=tailScore z Y H z := by simpa only [tailScore_at_join] using hzjoin
  have hc := concaveOn_joinAt hlz hz.le hpsi (tailScore_concave z Y H hz htwo)
    hjoin hpsiD htailD hjump
  apply hc.congr
  intro r hr
  have hxz := hxl.trans hlz
  have hj : headScore x J f x=joinAt z psi (tailScore z Y H) x := by
    rw [headScore_at_join x J f hx,joinAt_left _ _ hxz,hxjoin]
  exact (joinAt_right _ _ (hxl.trans hr.1) hj).symm

end OptimalG
