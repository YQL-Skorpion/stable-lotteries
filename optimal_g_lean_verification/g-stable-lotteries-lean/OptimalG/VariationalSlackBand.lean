import OptimalG.VariationalSlopeIntegration
import Mathlib.Topology.Order.IntermediateValue

/-! A first-contact argument for the slack band in B.3. The strict initial
margin is essential: the derivative condition only applies inside the band. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

 theorem lipschitz_nonnegative_stays_below {a b C : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hstart : f a < C)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ f r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b),
      0 < f r → f r ≤ C → deriv f r ≤ 0) :
    ∀ t ∈ Icc a b, f t < C := by
  intro t ht
  by_contra hn
  obtain ⟨q,hq,hfq⟩ := intermediate_value_Icc ht.1
    hf.continuous.continuousOn (show C ∈ Icc (f a) (f t) from ⟨hstart.le,le_of_not_gt hn⟩)
  let T : Set ℝ := Icc a t ∩ f ⁻¹' {C}
  have hT : IsCompact T := isCompact_Icc.inter_right
    (isClosed_singleton.preimage hf.continuous)
  obtain ⟨s,hs,hmin⟩ := hT.exists_isMinOn (show T.Nonempty from ⟨q,hq,hfq⟩)
    continuous_id.continuousOn
  have hfs : f s = C := hs.2
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl (hs.1.2.trans ht.2)
  have hband : ∀ r ∈ Icc a s, f r ≤ C := by
    intro r hr
    by_contra hn'
    obtain ⟨v,hv,hfv⟩ := intermediate_value_Icc hr.1 hf.continuous.continuousOn
      (show C ∈ Icc (f a) (f r) from ⟨hstart.le,(lt_of_not_ge hn').le⟩)
    have hvs : s ≤ v := hmin (show v ∈ T from ⟨⟨hv.1,hv.2.trans (hr.2.trans hs.1.2)⟩,hfv⟩)
    have hrs : r = s := le_antisymm hr.2 (hvs.trans hv.2)
    exact hn' (by simpa [hrs,hfs])
  have hmono := lipschitz_nonnegative_slack_antitone
    (hf.lipschitzOnWith : LipschitzOnWith K f (Icc a s)) (show (0:ℝ) ≤ 0 by rfl)
    (fun r hr => hpos r (hsub hr)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae_restrict_of_subset hsub hd] with r hr hder
      intro hfr
      simpa using hder hfr (hband r hr))
  have hh := hmono ⟨le_rfl,hs.1.1⟩ ⟨hs.1.1,le_rfl⟩ hs.1.1
  exact (not_le_of_gt hstart) (by simpa [hfs] using hh)

 theorem lipschitz_nonnegative_band_decay {a b C gamma : ℝ} {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hstart : f a < C) (hgamma : 0 ≤ gamma)
    (hpos : ∀ r ∈ Icc a b, 0 ≤ f r)
    (hd : ∀ᵐ r ∂volume.restrict (Icc a b),
      0 < f r → f r ≤ C → deriv f r ≤ -gamma) :
    (∀ t ∈ Icc a b, f t < C) ∧ AntitoneOn f (Icc a b) ∧
      ∀ t ∈ Icc a b, f t ≤ max 0 (f a-gamma*(t-a)) := by
  have hband := lipschitz_nonnegative_stays_below hf hstart hpos (by
    filter_upwards [hd] with r hr hp hb
    linarith [hr hp hb])
  have hder : ∀ᵐ r ∂volume.restrict (Icc a b), 0 < f r → deriv f r ≤ -gamma := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,hd] with r hr hder hp
    exact hder hp (hband r hr).le
  exact ⟨hband,lipschitz_nonnegative_slack_antitone hf.lipschitzOnWith hgamma hpos hder,
    lipschitz_nonnegative_slack_decay hf.lipschitzOnWith hgamma hpos hder⟩

end OptimalG.Variational
