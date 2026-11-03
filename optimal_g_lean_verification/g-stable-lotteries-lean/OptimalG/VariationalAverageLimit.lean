import OptimalG.VariationalControlLimit
import OptimalG.VariationalPullback

/-! Continuity of actual averaged rational controls under admissible data limits. -/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped Topology

theorem Admissible.control_coefficients_measurable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (z u : ℝ) :
    AEStronglyMeasurable (controlCoeffX lam d z u) controlMeasure ∧
      AEStronglyMeasurable (controlCoeffY lam d z u) controlMeasure := by
  have hR := h.control_primitive_measurable
  have hp : AEStronglyMeasurable (fun c : Control => c.1) controlMeasure :=
    measurable_fst.aestronglyMeasurable
  have hx : AEStronglyMeasurable (fun c : Control => c.2.1) controlMeasure :=
    (measurable_fst.comp measurable_snd).aestronglyMeasurable
  have hy : AEStronglyMeasurable (fun c : Control => c.2.2) controlMeasure :=
    (measurable_snd.comp measurable_snd).aestronglyMeasurable
  have hP : AEStronglyMeasurable (fun c : Control => quadratic lam (1-c.1)-d.S) controlMeasure := by
    dsimp [quadratic]
    fun_prop
  have hQ : AEStronglyMeasurable (fun c : Control => quadratic lam (z-c.1)-d.S-u) controlMeasure := by
    dsimp [quadratic]
    fun_prop
  have hk := (hp.add hy).sub (aestronglyMeasurable_const (b:=lam))
  have hh := (aestronglyMeasurable_const (b:=2*lam)).sub hx
  have hD := (hh.mul hR).sub (hk.mul hP)
  exact ⟨((aestronglyMeasurable_const.mul hR).add (hQ.mul hk)).neg.div₀ hD,
    ((aestronglyMeasurable_const.mul hP).add (hQ.mul hh)).neg.div₀ hD⟩

theorem control_x_map_absolutelyContinuous {ν : Measure Control} (hν : ν ≪ controlMeasure) :
    ν.map (fun c => c.2.1) ≪ volume.restrict (Icc ell tEnd) := by
  apply absolutelyContinuous_map_of_ae_lift (measurable_fst.comp measurable_snd)
  intro P hP
  exact hν.ae_le ((ae_control_lowRanks P hP).mono fun _ h => h.1)

theorem control_y_map_absolutelyContinuous {ν : Measure Control} (hν : ν ≪ controlMeasure) :
    ν.map (fun c => c.2.2) ≪ volume.restrict (Icc ell tEnd) := by
  apply absolutelyContinuous_map_of_ae_lift (measurable_snd.comp measurable_snd)
  intro P hP
  exact hν.ae_le ((ae_control_lowRanks P hP).mono fun _ h => h.2)

theorem Admissible.control_terms_integrable {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {ν : Measure Control} [IsFiniteMeasure ν]
    (hν : ν ≪ controlMeasure) (z u : ℝ) :
    Integrable (fun c => controlCoeffX lam d z u c*d.phi c.2.1) ν ∧
      Integrable (fun c => controlCoeffY lam d z u c*d.phi c.2.2) ν := by
  have hmem : ∀ᵐ c ∂ν, c ∈ controlDomain := hν.ae_le (ae_restrict_mem controlDomain_measurable)
  have hc : ∀ᵐ c ∂ν, ‖controlCoeffX lam d z u c‖ ≤ controlCoeffBound z u ∧
      ‖controlCoeffY lam d z u c‖ ≤ controlCoeffBound z u := by
    filter_upwards [hmem] with c hc
    simpa only [Real.norm_eq_abs] using h.control_coefficients_bound z u hc
  have hp : ∀ᵐ c ∂ν, ‖d.phi c.2.1‖ ≤ (1:ℝ)/3 ∧ ‖d.phi c.2.2‖ ≤ (1:ℝ)/3 :=
    hν.ae_le (ae_control_lowRanks _ h.phi_norm_bound)
  have hm := h.control_coefficients_measurable z u
  have hs := h.control_scores_measurable
  have hx : Integrable (controlCoeffX lam d z u) ν :=
    (integrable_const (controlCoeffBound z u)).mono' (hm.1.mono_ac hν) (hc.mono fun _ h => h.1)
  have hy : Integrable (controlCoeffY lam d z u) ν :=
    (integrable_const (controlCoeffBound z u)).mono' (hm.2.mono_ac hν) (hc.mono fun _ h => h.2)
  exact ⟨hx.mul_bdd (hs.1.mono_ac hν) (hp.mono fun _ h => h.1),
    hy.mul_bdd (hs.2.mono_ac hν) (hp.mono fun _ h => h.2)⟩

/-- Every fixed absolutely continuous finite average of the genuine controls
converges under scalar convergence and uniform convergence of low primitives. -/
theorem average_controlH_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (ν : Measure Control) [IsFiniteMeasure ν] (hν : ν ≪ controlMeasure) (z u : ℝ) :
    Tendsto (fun n => ∫ c, controlH (lamn n) (dn n) z u c ∂ν) atTop
      (𝓝 (∫ c, controlH lam d z u c ∂ν)) := by
  have hmem : ∀ᵐ c ∂ν, c ∈ controlDomain := hν.ae_le (ae_restrict_mem controlDomain_measurable)
  have hB : 0 ≤ controlCoeffBound z u := by unfold controlCoeffBound; positivity
  have hbounds (n : ℕ) : ∀ᵐ c ∂ν,
      ‖controlCoeffX (lamn n) (dn n) z u c‖ ≤ controlCoeffBound z u ∧
      ‖controlCoeffY (lamn n) (dn n) z u c‖ ≤ controlCoeffBound z u := by
    filter_upwards [hmem] with c hc
    simpa only [Real.norm_eq_abs] using (hn n).control_coefficients_bound z u hc
  have hlim : ∀ᵐ c ∂ν,
      Tendsto (fun n => controlCoeffX (lamn n) (dn n) z u c) atTop (𝓝 (controlCoeffX lam d z u c)) ∧
      Tendsto (fun n => controlCoeffY (lamn n) (dn n) z u c) atTop (𝓝 (controlCoeffY lam d z u c)) := by
    filter_upwards [hmem] with c hc
    exact control_coefficients_tendsto_of_data lamn dn hn hd hlam hS hJ z u hc
  have hweak (g : ℝ → ℝ) (hg : Integrable g (volume.restrict (Icc ell tEnd))) :
      Tendsto (fun n => ∫ x, g x*(dn n).phi x ∂volume.restrict (Icc ell tEnd)) atTop
        (𝓝 (∫ x, g x*d.phi x ∂volume.restrict (Icc ell tEnd))) := by
    simpa only [mul_comm] using score_tests_tendsto_of_primitive_convergence lamn dn hn hd hJ g hg
  have hX := tendsto_integral_varying_weighted_pullback
    (measurable_fst.comp measurable_snd) (control_x_map_absolutelyContinuous hν)
    (fun n => controlCoeffX (lamn n) (dn n) z u) (controlCoeffX lam d z u)
    (fun n => ((hn n).control_coefficients_measurable z u).1.mono_ac hν)
    ((hd.control_coefficients_measurable z u).1.mono_ac hν)
    (controlCoeffBound z u) hB (fun n => (hbounds n).mono fun _ h => h.1)
    (hlim.mono fun _ h => h.1) (fun n => (dn n).phi) d.phi
    (fun n => (hn n).2.2.1.aestronglyMeasurable) hd.2.2.1.aestronglyMeasurable
    (1/3) (by norm_num) (fun n => (hn n).phi_norm_bound) hd.phi_norm_bound hweak
  have hY := tendsto_integral_varying_weighted_pullback
    (measurable_snd.comp measurable_snd) (control_y_map_absolutelyContinuous hν)
    (fun n => controlCoeffY (lamn n) (dn n) z u) (controlCoeffY lam d z u)
    (fun n => ((hn n).control_coefficients_measurable z u).2.mono_ac hν)
    ((hd.control_coefficients_measurable z u).2.mono_ac hν)
    (controlCoeffBound z u) hB (fun n => (hbounds n).mono fun _ h => h.2)
    (hlim.mono fun _ h => h.2) (fun n => (dn n).phi) d.phi
    (fun n => (hn n).2.2.1.aestronglyMeasurable) hd.2.2.1.aestronglyMeasurable
    (1/3) (by norm_num) (fun n => (hn n).phi_norm_bound) hd.phi_norm_bound hweak
  have heq {L : ℝ} {D : LowRankData} (h : Admissible L D) :
      (∫ c, controlCoeffX L D z u c*D.phi c.2.1 ∂ν) +
        (∫ c, controlCoeffY L D z u c*D.phi c.2.2 ∂ν) = ∫ c, controlH L D z u c ∂ν := by
    have hi := h.control_terms_integrable hν z u
    rw [← integral_add hi.1 hi.2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun c => (controlH_linear_scores L D z u c).symm
  simpa only [Function.comp_apply,heq hd,heq (hn _)] using hX.add hY

/-- Four fixed evaluations recover every time/state evaluation exactly. -/
theorem controlH_quadratic_interpolation (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) :
    controlH lam d z u c =
      (controlH lam d 1 0 c+controlH lam d (-1) 0 c-2*controlH lam d 0 0 c)*(z^2/2) +
      (controlH lam d 1 0 c-controlH lam d (-1) 0 c)*(z/2) +
      (controlH lam d 0 1 c-controlH lam d 0 0 c)*u + controlH lam d 0 0 c := by
  unfold controlH quadratic
  ring

theorem Admissible.average_controlH_quadratic {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) {ν : Measure Control} [IsFiniteMeasure ν]
    (hν : ν ≪ controlMeasure) (z u : ℝ) :
    (∫ c, controlH lam d z u c ∂ν) =
      ((∫ c, controlH lam d 1 0 c ∂ν)+(∫ c, controlH lam d (-1) 0 c ∂ν)-
        2*(∫ c, controlH lam d 0 0 c ∂ν))*(z^2/2) +
      ((∫ c, controlH lam d 1 0 c ∂ν)-(∫ c, controlH lam d (-1) 0 c ∂ν))*(z/2) +
      ((∫ c, controlH lam d 0 1 c ∂ν)-(∫ c, controlH lam d 0 0 c ∂ν))*u +
        (∫ c, controlH lam d 0 0 c ∂ν) := by
  have hi (a b : ℝ) : Integrable (controlH lam d a b) ν :=
    ((h.controlH_bounded a b).of_absolutelyContinuous hν).integrable
      ((h.controlH_measurable a b).mono_ac hν)
  let A := fun c => controlH lam d 1 0 c+controlH lam d (-1) 0 c-2*controlH lam d 0 0 c
  let B := fun c => controlH lam d 1 0 c-controlH lam d (-1) 0 c
  let C := fun c => controlH lam d 0 1 c-controlH lam d 0 0 c
  have hA : Integrable A ν := ((hi 1 0).add (hi (-1) 0)).sub ((hi 0 0).const_mul 2)
  have hB : Integrable B ν := (hi 1 0).sub (hi (-1) 0)
  have hC : Integrable C ν := (hi 0 1).sub (hi 0 0)
  have heq : controlH lam d z u =
      fun c => A c*(z^2/2)+B c*(z/2)+C c*u+controlH lam d 0 0 c := by
    funext c
    exact controlH_quadratic_interpolation lam d z u c
  have hAB : Integrable (fun c => A c*(z^2/2)+B c*(z/2)) ν :=
    (hA.mul_const (z^2/2)).add (hB.mul_const (z/2))
  have hABC : Integrable (fun c => A c*(z^2/2)+B c*(z/2)+C c*u) ν := hAB.add (hC.mul_const u)
  rw [heq, integral_add hABC (hi 0 0), integral_add hAB (hC.mul_const u),
    integral_add (hA.mul_const (z^2/2)) (hB.mul_const (z/2))]
  simp only [integral_mul_const]
  have ha : (∫ c, A c ∂ν) = (∫ c, controlH lam d 1 0 c ∂ν)+
      (∫ c, controlH lam d (-1) 0 c ∂ν)-2*(∫ c, controlH lam d 0 0 c ∂ν) := by
    dsimp [A]
    have hsum : Integrable (fun c => controlH lam d 1 0 c+controlH lam d (-1) 0 c) ν :=
      (hi 1 0).add (hi (-1) 0)
    rw [integral_sub hsum ((hi 0 0).const_mul 2),
      integral_add (hi 1 0) (hi (-1) 0),integral_const_mul]
  have hb : (∫ c, B c ∂ν) = (∫ c, controlH lam d 1 0 c ∂ν)-
      (∫ c, controlH lam d (-1) 0 c ∂ν) := integral_sub (hi 1 0) (hi (-1) 0)
  have hc : (∫ c, C c ∂ν) = (∫ c, controlH lam d 0 1 c ∂ν)-
      (∫ c, controlH lam d 0 0 c ∂ν) := integral_sub (hi 0 1) (hi 0 0)
  rw [ha,hb,hc]

/-- Joint continuity along admissible data and converging time/state sequences. -/
theorem average_controlH_tendsto_of_data_state
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (ν : Measure Control) [IsFiniteMeasure ν] (hν : ν ≪ controlMeasure)
    (zn un : ℕ → ℝ) {z u : ℝ} (hz : Tendsto zn atTop (𝓝 z)) (hu : Tendsto un atTop (𝓝 u)) :
    Tendsto (fun n => ∫ c, controlH (lamn n) (dn n) (zn n) (un n) c ∂ν) atTop
      (𝓝 (∫ c, controlH lam d z u c ∂ν)) := by
  have ht := average_controlH_tendsto_of_data lamn dn hn hd hlam hS hJ ν hν
  have hall := (((((ht 1 0).add (ht (-1) 0)).sub ((ht 0 0).const_mul 2)).mul ((hz.pow 2).div_const 2)).add
    (((ht 1 0).sub (ht (-1) 0)).mul (hz.div_const 2))).add
      (((ht 0 1).sub (ht 0 0)).mul hu) |>.add (ht 0 0)
  rw [← hd.average_controlH_quadratic hν z u] at hall
  exact hall.congr' (Filter.Eventually.of_forall fun n =>
    ((hn n).average_controlH_quadratic hν (zn n) (un n)).symm)

end OptimalG.Variational
