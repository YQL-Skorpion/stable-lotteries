import OptimalG.VariationalFeatureSupport
import OptimalG.SignedRationalControl

/-! A raw rational field extends to the same rank/score support even when
its parameter and primitive have changed. This retains the boundary controls
needed by rank matching for a transferred competitor. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

noncomputable def rawFeatureH (L : ℝ) (J : ℝ → ℝ) (z u : ℝ) (v : ControlFeature) : ℝ :=
  -((z-L)*(J v.1.1*v.2.1+J (1-v.1.1)*v.2.2)+
      (J (z-v.1.1)-u)*((v.1.1+v.1.2.2-L)*v.2.1+(2*L-v.1.2.1)*v.2.2))/
    max 0.0519 (rawDet L J v.1)

theorem rawFeatureH_continuous {L : ℝ} {J : ℝ → ℝ} (hJ : Continuous J) (z u : ℝ) :
    Continuous (rawFeatureH L J z u) := by
  unfold rawFeatureH rawDet
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro v
  have hh : (0.0519 : ℝ) ≤ max 0.0519
      ((2*L-v.1.2.1)*J v.1.1-(v.1.1+v.1.2.2-L)*J (1-v.1.1)) := le_max_left _ _
  linarith

theorem rawFeatureH_eq_value {L : ℝ} {J : ℝ → ℝ} (z u : ℝ) (v : ControlFeature)
    (hdet : 0.0519 ≤ rawDet L J v.1) :
    rawFeatureH L J z u v=Certificates.Control.value (z-L) (2*L-v.1.2.1)
      (v.1.1+v.1.2.2-L) (J v.1.1) (J (1-v.1.1)) (J (z-v.1.1)-u) v.2.1 v.2.2 := by
  rw [rawFeatureH,max_eq_right hdet]
  rfl

theorem rawFeatureH_map_eq {L : ℝ} {J : ℝ → ℝ} (d : LowRankData) (z u : ℝ)
    {c : Control} (hdet : 0.0519 ≤ rawDet L J c) :
    rawFeatureH L J z u (controlFeatureMap d c)=
      signedControlH L J (rawAlpha L J d.phi) (rawBeta L J d.phi) (·.1) z u c := by
  rw [rawFeatureH_eq_value z u _ hdet,rawControl_eq_value]
  rfl

theorem rawVectorField_le_feature {lam L : ℝ} {d : LowRankData} {J : ℝ → ℝ} {K : ℝ≥0}
    (hd : Admissible lam d) (hJ : LipschitzWith K J)
    (hdet : ∀ c ∈ controlDomain,0.0519 ≤ rawDet L J c)
    (z u : ℝ) {v : ControlFeature} (hv : v ∈ controlFeatureSupport d) :
    rawVectorField L J d.phi z u ≤ rawFeatureH L J z u v := by
  have hs := hd.control_basic_bounded
  have hcoeff := raw_coefficients_bounded hJ (by norm_num : (0 : ℝ) < 0.0519) hdet
    hs.2.2.1 hs.2.2.2.1
  have hb := signedControlH_bounded (lam := L) hJ hcoeff.1 hcoeff.2 control_coordinates_bounded.1 z u
  have hc := rawFeatureH_continuous (L := L) hJ.continuous z u
  apply (min_le_right _ _).trans
  apply (controlFeatureMeasure d).support_subset_of_isClosed (isClosed_le continuous_const hc) _ hv
  apply (ae_map_iff hd.controlFeatureMap_aemeasurable (isClosed_le continuous_const hc).measurableSet).mpr
  filter_upwards [ae_restrict_mem controlDomain_measurable,ae_essInf_le hb.boundedBelow] with c hdom hlow
  rwa [rawFeatureH_map_eq d z u (hdet c hdom)]

end OptimalG.Variational
