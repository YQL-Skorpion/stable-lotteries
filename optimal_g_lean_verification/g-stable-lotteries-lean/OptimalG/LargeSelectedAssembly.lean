import OptimalG.LargeSelectedMassMonotone
import OptimalG.LargeSelectedFixedMass
import OptimalG.LargeSelectedNormalization

/-! The finite large-mass selected-strip signs imply the actual normalized
mixed test, using monotonicity in mass and all-split coverage at .65. -/
namespace OptimalG
open Set Variational Certificates.LargeSelectedExpressions

structure LargeSelectedSigns (lam S : ℝ) : Prop where
  derivative : LargeSelectedDerivativeSigns lam S
  rank : ∀ z∈Icc (391/500:ℝ) (7/8),LargeSelectedRankSigns lam S z
  cubicUpper : cubic lam S (7/8)≤13/200
  smallSplit : ∀ z∈Icc (391/500:ℝ) (7/8),smallSplitK lam S z≤0

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem largeSelected_of_signs {S c p z q Y H : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hp : p∈Icc (13/20:ℝ) (7/8)) (hz : z∈Icc (391/500:ℝ) (7/8)) (hpz : p≤z)
    (hq : q∈Icc (0:ℝ) lam)
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S)
    (hline : ∀ r∈Icc (9/25:ℝ) (391/500),phi r=lam-r)
    (hcapOrder : ∀ u∈Icc (0:ℝ) (9/25),∀ v∈Icc (0:ℝ) (9/25),u≤v→
      Certificates.SmallMassExpressions.slope lam S*(v-u)≤capScore lam S v-capScore lam S u)
    (hY : 8793/100000≤Y) (hH : -(3589/10000)≤H)
    (hfinish : curvePrimitive phi (7/8)=tailPrimitive (539/625) Y H (7/8))
    (hm : 0≤Certificates.LineControl.slope lam S)
    (hdef : cubic lam S z≤scoreDefect phi lam z)
    (hn : LargeSelectedSigns lam S) :
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z≤0 := by
  have he : cubic lam S z≤13/200 :=
    (cubicControlDeficit_monotone hm _ _ hz.2).trans hn.cubicUpper
  have hant := g.largeSelected_mass_antitone h hS hi hz hq he hn.derivative
  have hbase := g.largeSelected_fixedMass_of_signs h hS hz hq hcapOrder (hn.rank z hz)
  have hnum := (hant (show (13/20:ℝ)∈Icc (13/20) z from
      ⟨le_rfl,hp.1.trans hpz⟩) ⟨hp.1,hpz⟩ hp.1).trans hbase
  exact h.largeSelected_of_numerator g hS hc hp hz hpz hq hi hline hY hH hfinish
    he hdef (hn.smallSplit z hz) hnum

end VerifierCurve
end OptimalG
