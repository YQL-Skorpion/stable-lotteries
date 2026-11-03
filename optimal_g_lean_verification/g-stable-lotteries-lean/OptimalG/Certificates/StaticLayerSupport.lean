import OptimalG.Certificates.StaticLayerPrimitive
import OptimalG.Certificates.StaticLayerFast

/-! Whole-layer supporting lines for the actual corrected trial, obtained from
kernel-checkable polynomial inequalities and exact branch semantics. -/
namespace OptimalG.Certificates.StaticSupport.ContinuousLayerCell
open RationalPolynomial Set
open StaticLow (lam slack leftContact rightContact)

noncomputable def supportCoefficient (c : ContinuousLayerCell) (t : ℝ) : ℝ :=
  c.Cnum.eval t/c.Cden.eval t

theorem checked_supports {c : ContinuousLayerCell}
    (hg : c.geometryCheck=true) (hn : c.fastNumericCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) {x y : ℝ}
    (hx : (0.2635:ℝ)≤x) (hy : (0.2635:ℝ)≤y) (hyp : c.pPoly.eval t≤y) :
    StaticLow.score x+c.supportCoefficient t*x≤c.A.eval t+c.supportCoefficient t*c.aPoly.eval t ∧
    StaticLow.score y+c.supportCoefficient t*y≤c.B.eval t+c.supportCoefficient t*c.bPoly.eval t := by
  have hs := geometry_score_values hg ht
  have ha := geometry_a_lower hg ht
  have hb := geometry_b_max hg ⟨ht.1.le,ht.2.le⟩
  rw [hs.1,hs.2,hb]
  by_cases hp : c.pinned=true
  · have hpin := fastNumericCheck_pin_bounds hn hp ⟨ht.1.le,ht.2.le⟩
    have hdat := (geometry_parts hg).2.2.2
    have hd : c.a0=leftContact ∧ c.a1=leftContact ∧ c.aPiece=0 ∧ c.bPiece=0 ∧ c.bIsA=true := by
      simpa only [if_pos hp] using hdat
    have he : c.aPoly.eval t=(leftContact:ℝ) := by simp [aPoly_eval,hd.1,hd.2.1]
    have hlo : StaticLow.slope leftContact≤-c.supportCoefficient t := by
      rw [StaticLow.slopeQ_cast] at hpin
      unfold supportCoefficient
      linarith [hpin.2]
    have hhi : -c.supportCoefficient t≤-(0.1:ℝ) := by
      unfold supportCoefficient
      linarith [hpin.1]
    have h1 := StaticLow.contact_support_head hlo hhi hx
    have h2 := StaticLow.contact_support_max_head hlo hhi hy hyp
    rw [he]
    constructor <;> nlinarith only [h1,h2]
  · have hC : c.supportCoefficient t=-StaticLow.slope (c.aPoly.eval t) :=
      geometry_free_coefficient hg hp ht
    have h1 := StaticLow.supporting_line_head ha hx
    have h2 := StaticLow.supporting_line_max_head ha hy hyp
    rw [hC]
    constructor <;> nlinarith only [h1,h2]

/-- This bounds every independent pair of root coordinates at every interior
point of the certified layer cell; the state and sign hypotheses are explicit. -/
theorem checked_lower {c : ContinuousLayerCell}
    (hg : c.geometryCheck=true) (hn : c.fastNumericCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) {U K x y : ℝ}
    (hU : 0≤U) (hK : 0≤K) (hx : (0.2635:ℝ)≤x) (hy : (0.2635:ℝ)≤y)
    (hyp : c.pPoly.eval t≤y)
    (hD : 0<Control.det (2*(lam:ℝ)-x) (c.pPoly.eval t+y-lam)
      (StaticLow.primitive (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack))
    (hcx : 0≤Control.cx U (c.pPoly.eval t+y-lam) (StaticLow.primitive (c.pPoly.eval t)) K)
    (hcy : 0≤Control.cy U (2*(lam:ℝ)-x) (quadratic lam (1-c.pPoly.eval t)-slack) K) :
    -U*c.Cu.eval t-K*c.alphau.eval t≤
      Control.value U (2*(lam:ℝ)-x) (c.pPoly.eval t+y-lam)
        (StaticLow.primitive (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack) K
        (StaticLow.score x) (StaticLow.score y) := by
  have hc := fastNumericCheck_sound hn ⟨ht.1.le,ht.2.le⟩
  rw [geometry_primitive_value hg ht,P_eval,h_eval,k_eval] at hc
  have hs := checked_supports hg hn ht hx hy hyp
  have hbalance : StaticLow.primitive (c.pPoly.eval t)*c.A.eval t+
      (quadratic lam (1-c.pPoly.eval t)-slack)*c.B.eval t≤
      c.supportCoefficient t*Control.det (2*(lam:ℝ)-c.aPoly.eval t)
        (c.pPoly.eval t+c.bPoly.eval t-lam) (StaticLow.primitive (c.pPoly.eval t))
        (quadratic lam (1-c.pPoly.eval t)-slack) := by
    simpa only [supportCoefficient,Control.det] using hc.2.1
  have hbase := Control.lower_of_common_support U lam (c.pPoly.eval t)
    (StaticLow.primitive (c.pPoly.eval t)) (quadratic lam (1-c.pPoly.eval t)-slack)
    K (c.supportCoefficient t) (c.aPoly.eval t) (c.bPoly.eval t) (c.A.eval t) (c.B.eval t)
    x y (StaticLow.score x) (StaticLow.score y) hc.1 hD hcx hcy hs.1 hs.2 hbalance
  exact Control.lower_of_coefficient_enclosures hU hK hc.2.2.1 hc.2.2.2 hbase

end OptimalG.Certificates.StaticSupport.ContinuousLayerCell
