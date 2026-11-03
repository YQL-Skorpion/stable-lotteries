import OptimalG.VariationalTransportFirstOrder

/-! The exact first-order transport identity for the constructed Stieltjes
matching. The initial atom remains in the singular integral. -/
namespace OptimalG.Variational
open Set MeasureTheory Function

 theorem transportPotential_interval_eq {a b r : ℝ} (hr : r ∈ Icc a b) (f : ℝ → ℝ) :
    transportPotential (volume.restrict (Icc a b)) f r = ∫ t in r..b, f t := by
  have he : Ici r ∩ Icc a b = Icc r b := by
    ext t
    constructor
    · intro ht; exact ⟨ht.1,ht.2.2⟩
    · intro ht; exact ⟨ht.1,hr.1.trans ht.1,ht.2⟩
  unfold transportPotential
  rw [Measure.restrict_restrict measurableSet_Ici,he,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hr.2]

 theorem stieltjes_cumulative_displacement (G : StieltjesFunction ℝ) {a b r : ℝ}
    (hleft : leftLim G a = a) (hr : r ∈ Icc a b) :
    (G.measure.restrict (Icc a b)).real (Iic r)-
      (volume.restrict (Icc a b)).real (Iic r) = G r-r := by
  have he : Iic r ∩ Icc a b = Icc a r := by
    ext t
    constructor
    · intro ht; exact ⟨ht.2.1,ht.1⟩
    · intro ht; exact ⟨ht.2,ht.1,ht.2.trans hr.2⟩
  rw [measureReal_restrict_apply measurableSet_Iic,measureReal_restrict_apply measurableSet_Iic,he]
  have hl : a ≤ G r := by rw [← hleft]; exact G.mono.leftLim_le hr.1
  rw [measureReal_def,G.measure_Icc,hleft,ENNReal.toReal_ofReal (sub_nonneg.mpr hl),
    Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr hr.1)]
  ring

 theorem stieltjes_first_order_transport (G : StieltjesFunction ℝ) {a b : ℝ}
    (hleft : leftLim G a = a) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    (∫ r in Icc a b, f r*(G r-r)) =
      (∫ r in Icc a b, (∫ t in r..b, f t)*(deriv G r-1))+
      (∫ r in Icc a b, (∫ t in r..b, f t) ∂G.measure.singularPart volume) := by
  letI : IsFiniteMeasure (G.measure.restrict (Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  let P := transportPotential (volume.restrict (Icc a b)) f
  have hPmu : IntegrableOn P (Icc a b) := cumulative_potential_integrable hf
  have hPG : IntegrableOn P (Icc a b) G.measure := cumulative_potential_integrable hf
  have hPw := integrableOn_transport_rn_mul G.measure volume measurableSet_Icc hPG
  have hPd : IntegrableOn (fun r => deriv G r*P r) (Icc a b) := by
    apply hPw.congr
    filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
    rw [hr]
  have hdecomp := setIntegral_transport_measure_decomposition G.measure volume measurableSet_Icc hPG
  have hfub := cumulative_displacement_fubini (nu:=G.measure.restrict (Icc a b)) hf
  have hleftIntegral : (∫ r in Icc a b, f r*(G r-r)) =
      (∫ r, f r*((G.measure.restrict (Icc a b)).real (Iic r)-
        (volume.restrict (Icc a b)).real (Iic r)) ∂volume.restrict (Icc a b)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [stieltjes_cumulative_displacement G hleft hr]
  rw [hleftIntegral,hfub]
  change (∫ r in Icc a b, P r ∂G.measure)-(∫ r in Icc a b, P r) = _
  rw [hdecomp]
  have hRN : (∫ r in Icc a b, (G.measure.rnDeriv volume r).toReal*P r) =
      ∫ r in Icc a b, deriv G r*P r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (stieltjes_deriv_rn_ae G)] with r hr
    rw [hr]
  rw [hRN]
  have hmain : (∫ r in Icc a b, (∫ t in r..b, f t)*(deriv G r-1)) =
      (∫ r in Icc a b, deriv G r*P r)-(∫ r in Icc a b, P r) := by
    calc
      _ = ∫ r in Icc a b, deriv G r*P r-P r := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hp : P r = ∫ t in r..b, f t := transportPotential_interval_eq hr f
        rw [hp]
        ring
      _ = _ := integral_sub hPd hPmu
  have hsing : (∫ r in Icc a b, (∫ t in r..b, f t) ∂G.measure.singularPart volume) =
      ∫ r in Icc a b, P r ∂G.measure.singularPart volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact (transportPotential_interval_eq hr f).symm
  rw [hmain,hsing]
  ring

end OptimalG.Variational
