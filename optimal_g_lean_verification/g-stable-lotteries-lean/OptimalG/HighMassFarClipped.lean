import OptimalG.FarClippedBounds
import OptimalG.HighMassGeometry

namespace OptimalG
open Set
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The actual normalized tail coefficient satisfies the complete bounded
far-clipped test; no separate interval subdivision is required. -/
theorem highMass_far_clipped {F slope : ℝ}
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=F+slope*r)
    (hslope : -(691/1000:ℝ)≤slope)
    (hfall : ∀ a b,0≤a→a≤b→b≤9/25→a-b≤phi b-phi a)
    (hcone : ∀ u∈Icc (22/25:ℝ) 1,
      -1+2*(1-u)≤phi u ∧ phi u≤-1+(67/10)*(1-u))
    {p x q : ℝ} (hp : p∈Ico (22/25:ℝ) 1)
    (hx : x∈Icc (9/50:ℝ) (9/25)) (hq : q∈Icc (0:ℝ) (9/50))
    (hv : 9/50≤x-q) :
    q-x+(p/curvePrimitive phi p)*(1-p)*(packingDelta phi p q/(1-p)-phi x)≤0 := by
  have ht := h.highMass_tail_coefficient hp
    (fun u hu => hcone u ⟨hp.1.trans hu.1,hu.2⟩)
  apply h.far_clipped_of_head hp hq hx hv hhead hslope hfall
  constructor
  · linarith only [ht.1]
  · simpa only [sub_sub_cancel] using ht.2

end VerifierCurve
end OptimalG
