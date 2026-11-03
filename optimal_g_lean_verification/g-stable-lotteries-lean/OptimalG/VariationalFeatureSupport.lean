import OptimalG.VariationalCapContact
import Mathlib.MeasureTheory.Measure.Support

/-!
# Compact essential graphs of rational controls

The pushforward support records ranks together with their score values. It is
compact even when the score is merely measurable, and continuous rational
controls extend their almost-everywhere envelope inequality to the full support.
-/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

noncomputable def controlPrimitiveExtension {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (r : ℝ) : ℝ :=
  if r ≤ ell then cap lam d.S (min r ell) else extendLowPrimitive (lowPrimitiveMap hd) r

theorem controlPrimitiveExtension_continuous {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : Continuous (controlPrimitiveExtension hd) := by
  have hc : Continuous (fun r : ℝ => cap lam d.S (min r ell)) := by
    unfold cap
    apply Continuous.sub (by fun_prop)
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro r
    have hh : min r ell ≤ (28 : ℝ)/100 := min_le_right _ _
    linarith
  have hJ := (extendLowPrimitive_lipschitz (lowPrimitiveMap hd) hd.lowPrimitive_lipschitz.to_restrict).continuous
  apply hc.if_le hJ continuous_id continuous_const
  intro r hr
  change r = ell at hr
  subst r
  rw [min_self,extendLowPrimitive_of_mem (lowPrimitiveMap hd) ⟨ell,by norm_num [ell,tEnd]⟩]
  exact (lowPrimitive_at_ell lam d).symm

theorem controlPrimitiveExtension_eq {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) {r : ℝ} (hr : r ∈ Icc pLo pHi) :
    controlPrimitiveExtension hd r = primitive lam d r := by
  unfold controlPrimitiveExtension primitive
  by_cases he : r ≤ ell
  · simp only [he,if_pos,min_eq_left he]
  · have ht : r ≤ tEnd := hr.2.trans (by norm_num [pHi,tEnd])
    simp only [he,if_neg,ht,if_pos,ite_false]
    exact extendLowPrimitive_of_mem (lowPrimitiveMap hd) ⟨r,⟨(lt_of_not_ge he).le,ht⟩⟩

abbrev ControlFeature := Control × (ℝ × ℝ)
noncomputable def controlFeatureMap (d : LowRankData) (c : Control) : ControlFeature :=
  (c,d.phi c.2.1,d.phi c.2.2)
noncomputable def controlFeatureMeasure (d : LowRankData) : Measure ControlFeature :=
  controlMeasure.map (controlFeatureMap d)
noncomputable def controlFeatureSupport (d : LowRankData) : Set ControlFeature :=
  (controlFeatureMeasure d).support
noncomputable def featureDet {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) (v : ControlFeature) : ℝ :=
  (2*lam-v.1.2.1)*controlPrimitiveExtension hd v.1.1-
    (v.1.1+v.1.2.2-lam)*(quadratic lam (1-v.1.1)-d.S)
noncomputable def featureH {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (z u : ℝ) (v : ControlFeature) : ℝ :=
  -((z-lam)*(controlPrimitiveExtension hd v.1.1*v.2.1+(quadratic lam (1-v.1.1)-d.S)*v.2.2)+
    (quadratic lam (z-v.1.1)-d.S-u)*((v.1.1+v.1.2.2-lam)*v.2.1+(2*lam-v.1.2.1)*v.2.2))/
      max (3/100) (featureDet hd v)

theorem featureH_continuous {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Continuous (fun w : (ℝ × ℝ) × ControlFeature => featureH hd w.1.1 w.1.2 w.2) := by
  have hR := controlPrimitiveExtension_continuous hd
  unfold featureH featureDet quadratic
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro w
    have hh : (3 : ℝ)/100 ≤ max (3/100)
        ((2*lam-w.2.1.2.1)*controlPrimitiveExtension hd w.2.1.1-
          (w.2.1.1+w.2.1.2.2-lam)*(lam*(1-w.2.1.1)-(1-w.2.1.1)^2/2-d.S)) := le_max_left _ _
    linarith

theorem featureH_map_eq {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (z u : ℝ) {c : Control} (hc : c ∈ controlDomain) :
    featureH hd z u (controlFeatureMap d c) = controlH lam d z u c := by
  unfold featureH featureDet controlFeatureMap
  dsimp only
  rw [controlPrimitiveExtension_eq hd hc.1]
  have hD := (hd.determinant_positive hc).le
  change _ / max (3/100) (controlDeterminant lam d c) = _
  rw [max_eq_right hD]
  rfl

theorem Admissible.controlFeatureMap_aemeasurable {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : AEMeasurable (controlFeatureMap d) controlMeasure :=
  measurable_id.aemeasurable.prodMk
    (hd.control_scores_measurable.1.aemeasurable.prodMk hd.control_scores_measurable.2.aemeasurable)

theorem Admissible.ae_mem_controlFeatureSupport {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    ∀ᵐ c ∂controlMeasure, controlFeatureMap d c ∈ controlFeatureSupport d :=
  ae_of_ae_map hd.controlFeatureMap_aemeasurable (controlFeatureMeasure d).support_mem_ae

theorem Admissible.controlFeatureSupport_subset {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    controlFeatureSupport d ⊆ controlDomain ×ˢ (Icc (0:ℝ) (278/1000) ×ˢ Icc (0:ℝ) (278/1000)) := by
  apply (controlFeatureMeasure d).support_subset_of_isClosed
    (controlDomain_isClosed.prod (isClosed_Icc.prod isClosed_Icc))
  apply (ae_map_iff hd.controlFeatureMap_aemeasurable
    (controlDomain_measurable.prod (measurableSet_Icc.prod measurableSet_Icc))).mpr
  filter_upwards [ae_restrict_mem controlDomain_measurable,hd.control_phi_bounds] with c hc hp
  exact ⟨hc,hp⟩

theorem Admissible.controlFeatureSupport_compact {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : IsCompact (controlFeatureSupport d) :=
  (controlDomain_isCompact.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset
    (controlFeatureMeasure d).isClosed_support hd.controlFeatureSupport_subset

theorem Admissible.controlFeatureSupport_nonempty {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : (controlFeatureSupport d).Nonempty := by
  obtain ⟨c,hc⟩ := hd.ae_mem_controlFeatureSupport.exists
  exact ⟨controlFeatureMap d c,hc⟩

/-- The actual essential-infimum bound extends to every point of the compact
support of the rank/score pushforward measure. -/
theorem Admissible.essInf_le_featureH {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (z u : ℝ) {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    essInf (controlH lam d z u) controlMeasure ≤ featureH hd z u v := by
  have hc : Continuous (featureH hd z u) := by
    exact (featureH_continuous hd).comp
      ((continuous_const : Continuous (fun _ : ControlFeature => (z,u))).prodMk continuous_id)
  apply (controlFeatureMeasure d).support_subset_of_isClosed
    (isClosed_le continuous_const hc) _ hv
  apply (ae_map_iff hd.controlFeatureMap_aemeasurable (isClosed_le continuous_const hc).measurableSet).mpr
  filter_upwards [ae_restrict_mem controlDomain_measurable,
    ae_essInf_le (hd.controlH_bounded z u).boundedBelow] with c hc hlow
  rwa [featureH_map_eq hd z u hc]

theorem Admissible.essInf_attained_in_featureSupport {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (z u : ℝ) :
    ∃ v ∈ controlFeatureSupport d,
      featureH hd z u v = essInf (controlH lam d z u) controlMeasure := by
  have hcont : Continuous (featureH hd z u) := by
    exact (featureH_continuous hd).comp
      ((continuous_const : Continuous (fun _ : ControlFeature => (z,u))).prodMk continuous_id)
  obtain ⟨v,hv,hmin⟩ := hd.controlFeatureSupport_compact.exists_isMinOn
    hd.controlFeatureSupport_nonempty hcont.continuousOn
  refine ⟨v,hv,le_antisymm ?_ (hd.essInf_le_featureH z u hv)⟩
  apply le_essInf_of_ae_le _ _ (hd.controlH_bounded z u).boundedAbove.isCoboundedUnder_ge
  filter_upwards [hd.ae_mem_controlFeatureSupport,ae_restrict_mem controlDomain_measurable] with c hc hdom
  rw [← featureH_map_eq hd z u hdom]
  exact hmin hc

end OptimalG.Variational
