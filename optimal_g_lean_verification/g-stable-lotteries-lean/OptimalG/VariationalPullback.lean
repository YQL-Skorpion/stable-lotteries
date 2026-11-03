import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak-star convergence under absolutely continuous weighted pullback

A measurable map with absolutely continuous pushforward transports every
integrable weight to an L¹ test density. The positive-weight argument uses the
Radon–Nikodym derivative of the weighted pushforward; signed weights are split
as `(w + |w|) - |w|`. No pointwise convergence of the score functions is needed.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace OptimalG.Variational

variable {I N : Type*} [MeasurableSpace I]
  {μ : Measure ℝ} [SigmaFinite μ] {ν : Measure I}
  {T : I → ℝ} {w : I → ℝ} {f : N → ℝ → ℝ} {f₀ : ℝ → ℝ} {l : Filter N}

omit [SigmaFinite μ] in
/-- An existing almost-everywhere lifting theorem directly supplies the
pushforward absolute-continuity premise. -/
theorem absolutelyContinuous_map_of_ae_lift (hT : Measurable T)
    (hlift : ∀ P : ℝ → Prop, (∀ᵐ x ∂μ, P x) → ∀ᵐ i ∂ν, P (T i)) : ν.map T ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  have hx : ∀ᵐ x ∂μ, x ∉ s := by simpa [ae_iff] using hzero
  have hy := hlift (fun x => x ∉ s) hx
  rw [Measure.map_apply hT hs]
  simpa [ae_iff,Set.preimage] using hy

theorem tendsto_integral_weighted_pullback_nonneg
    (hT : Measurable T) (hac : ν.map T ≪ μ)
    (hw : Integrable w ν) (hw0 : ∀ᵐ i ∂ν, 0 ≤ w i)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hf₀ : AEStronglyMeasurable f₀ μ)
    (hweak : ∀ g : ℝ → ℝ, Integrable g μ →
      Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 (∫ x, g x * f₀ x ∂μ))) :
    Tendsto (fun n => ∫ i, w i * f n (T i) ∂ν) l (𝓝 (∫ i, w i * f₀ (T i) ∂ν)) := by
  let νw : Measure I := ν.withDensity (fun i => ENNReal.ofReal (w i))
  haveI : IsFiniteMeasure νw := isFiniteMeasure_withDensity_ofReal hw.2
  let ρ : Measure ℝ := νw.map T
  haveI : IsFiniteMeasure ρ := inferInstance
  have hρ : ρ ≪ μ := ((withDensity_absolutelyContinuous ν _).map hT).trans hac
  let g : ℝ → ℝ := fun x => (ρ.rnDeriv μ x).toReal
  have hg : Integrable g μ := Measure.integrable_toReal_rnDeriv
  have heq (F : ℝ → ℝ) (hF : AEStronglyMeasurable F μ) :
      (∫ x, g x * F x ∂μ) = ∫ i, w i * F (T i) ∂ν := by
    calc
      (∫ x, g x * F x ∂μ) = ∫ x, F x ∂ρ := integral_toReal_rnDeriv_mul hρ
      _ = ∫ i, F (T i) ∂νw := integral_map hT.aemeasurable (hF.mono_ac hρ)
      _ = ∫ i, (ENNReal.ofReal (w i)).toReal * F (T i) ∂ν :=
        integral_withDensity_eq_integral_toReal_smul₀ hw.1.aemeasurable.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
      _ = ∫ i, w i * F (T i) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hw0] with i hi
        rw [ENNReal.toReal_ofReal hi]
  simpa only [heq _ hf₀, heq _ (hf _)] using hweak g hg

/-- Integrable signed weights are allowed; boundedness of the functions ensures
that the two positive-weight integrals can be subtracted. -/
theorem tendsto_integral_weighted_pullback
    (hT : Measurable T) (hac : ν.map T ≪ μ) (hw : Integrable w ν)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hf₀ : AEStronglyMeasurable f₀ μ)
    (C : ℝ) (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) (hb₀ : ∀ᵐ x ∂μ, ‖f₀ x‖ ≤ C)
    (hweak : ∀ g : ℝ → ℝ, Integrable g μ →
      Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 (∫ x, g x * f₀ x ∂μ))) :
    Tendsto (fun n => ∫ i, w i * f n (T i) ∂ν) l (𝓝 (∫ i, w i * f₀ (T i) ∂ν)) := by
  have hqp : Measure.QuasiMeasurePreserving T ν μ := ⟨hT,hac⟩
  have hwp : Integrable (fun i => w i+|w i|) ν := hw.add hw.abs
  have hp := tendsto_integral_weighted_pullback_nonneg hT hac hwp
    (Filter.Eventually.of_forall fun i => by linarith [neg_abs_le (w i)]) hf hf₀ hweak
  have hm := tendsto_integral_weighted_pullback_nonneg hT hac hw.abs
    (Filter.Eventually.of_forall fun i => abs_nonneg (w i)) hf hf₀ hweak
  have heq (F : ℝ → ℝ) (hF : AEStronglyMeasurable F μ) (hFb : ∀ᵐ x ∂μ, ‖F x‖ ≤ C) :
      (∫ i, (w i+|w i|) * F (T i) ∂ν) - (∫ i, |w i| * F (T i) ∂ν) =
        ∫ i, w i * F (T i) ∂ν := by
    have hcomp : AEStronglyMeasurable (fun i => F (T i)) ν := hF.comp_quasiMeasurePreserving hqp
    have hbcomp : ∀ᵐ i ∂ν, ‖F (T i)‖ ≤ C := hqp.ae hFb
    rw [← integral_sub (hwp.mul_bdd hcomp hbcomp) (hw.abs.mul_bdd hcomp hbcomp)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun i => by ring
  simpa only [heq _ hf₀ hb₀, heq _ (hf _) (hb _)] using hp.sub hm

/-- Convenient finite-measure version with a bounded measurable weight. -/
theorem tendsto_integral_bounded_weighted_pullback [IsFiniteMeasure ν]
    (hT : Measurable T) (hac : ν.map T ≪ μ)
    (hw : AEStronglyMeasurable w ν) (B : ℝ) (hwB : ∀ᵐ i ∂ν, ‖w i‖ ≤ B)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hf₀ : AEStronglyMeasurable f₀ μ)
    (C : ℝ) (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) (hb₀ : ∀ᵐ x ∂μ, ‖f₀ x‖ ≤ C)
    (hweak : ∀ g : ℝ → ℝ, Integrable g μ →
      Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 (∫ x, g x * f₀ x ∂μ))) :
    Tendsto (fun n => ∫ i, w i * f n (T i) ∂ν) l (𝓝 (∫ i, w i * f₀ (T i) ∂ν)) := by
  have hwi : Integrable w ν := (integrable_const B).mono' hw hwB
  exact tendsto_integral_weighted_pullback hT hac hwi hf hf₀ C hb hb₀ hweak

/-- The averaged-control coefficients may vary: almost-everywhere convergence
and a common finite bound suffice. The scores themselves only converge weakly. -/
theorem tendsto_integral_varying_weighted_pullback [IsFiniteMeasure ν]
    (hT : Measurable T) (hac : ν.map T ≪ μ)
    (wn : ℕ → I → ℝ) (w₀ : I → ℝ)
    (hwn : ∀ n, AEStronglyMeasurable (wn n) ν) (hw₀ : AEStronglyMeasurable w₀ ν)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ n, ∀ᵐ i ∂ν, ‖wn n i‖ ≤ B)
    (hwlim : ∀ᵐ i ∂ν, Tendsto (fun n => wn n i) atTop (𝓝 (w₀ i)))
    (fs : ℕ → ℝ → ℝ) (fs₀ : ℝ → ℝ)
    (hfs : ∀ n, AEStronglyMeasurable (fs n) μ) (hfs₀ : AEStronglyMeasurable fs₀ μ)
    (C : ℝ) (_hC : 0 ≤ C)
    (hfb : ∀ n, ∀ᵐ x ∂μ, ‖fs n x‖ ≤ C) (hfb₀ : ∀ᵐ x ∂μ, ‖fs₀ x‖ ≤ C)
    (hweak : ∀ g : ℝ → ℝ, Integrable g μ →
      Tendsto (fun n => ∫ x, g x * fs n x ∂μ) atTop (𝓝 (∫ x, g x * fs₀ x ∂μ))) :
    Tendsto (fun n => ∫ i, wn n i * fs n (T i) ∂ν) atTop
      (𝓝 (∫ i, w₀ i * fs₀ (T i) ∂ν)) := by
  have hqp : Measure.QuasiMeasurePreserving T ν μ := ⟨hT,hac⟩
  have hwbAll : ∀ᵐ i ∂ν, ∀ n, ‖wn n i‖ ≤ B := ae_all_iff.mpr hwb
  have hw₀b : ∀ᵐ i ∂ν, ‖w₀ i‖ ≤ B := by
    filter_upwards [hwbAll,hwlim] with i hi hlim
    exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hi)
  have hfcomp (n : ℕ) : AEStronglyMeasurable (fun i => fs n (T i)) ν :=
    (hfs n).comp_quasiMeasurePreserving hqp
  have hfbcomp (n : ℕ) : ∀ᵐ i ∂ν, ‖fs n (T i)‖ ≤ C := hqp.ae (hfb n)
  have hfbAll : ∀ᵐ i ∂ν, ∀ n, ‖fs n (T i)‖ ≤ C := ae_all_iff.mpr hfbcomp
  have hfixed := tendsto_integral_bounded_weighted_pullback hT hac hw₀ B hw₀b
    hfs hfs₀ C hfb hfb₀ hweak
  let e : ℕ → I → ℝ := fun n i => (wn n i-w₀ i)*fs n (T i)
  have heMeas (n : ℕ) : AEStronglyMeasurable (e n) ν := (hwn n |>.sub hw₀).mul (hfcomp n)
  have heBound (n : ℕ) : ∀ᵐ i ∂ν, ‖e n i‖ ≤ 2*B*C := by
    filter_upwards [hwb n,hw₀b,hfbcomp n] with i hi hi₀ hfi
    change ‖(wn n i-w₀ i)*fs n (T i)‖ ≤ 2*B*C
    rw [norm_mul]
    have hnorm : ‖wn n i-w₀ i‖ ≤ 2*B := (norm_sub_le _ _).trans (by linarith)
    exact mul_le_mul hnorm hfi (norm_nonneg _) (by positivity)
  have heLim : ∀ᵐ i ∂ν, Tendsto (fun n => e n i) atTop (𝓝 0) := by
    filter_upwards [hwlim,hfbAll] with i hwi hfi
    have hlim : Tendsto (fun n => ‖wn n i-w₀ i‖*C) atTop (𝓝 0) := by
      simpa using (hwi.sub (tendsto_const_nhds (x:=w₀ i))).norm.mul_const C
    refine squeeze_zero_norm (a := fun n => ‖wn n i-w₀ i‖*C) ?_ hlim
    intro n
    change ‖(wn n i-w₀ i)*fs n (T i)‖ ≤ ‖wn n i-w₀ i‖*C
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hfi n) (norm_nonneg _)
  have heInt (n : ℕ) : Integrable (e n) ν :=
    (integrable_const (2*B*C)).mono' (heMeas n) (heBound n)
  have heConv : Tendsto (fun n => ∫ i, e n i ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence (fun _ => 2*B*C)
      heMeas (integrable_const _) heBound heLim
  have hw₀Int : Integrable w₀ ν := (integrable_const B).mono' hw₀ hw₀b
  have heq (n : ℕ) : (∫ i, w₀ i*fs n (T i) ∂ν) + (∫ i, e n i ∂ν) =
      ∫ i, wn n i*fs n (T i) ∂ν := by
    rw [← integral_add (hw₀Int.mul_bdd (hfcomp n) (hfbcomp n)) (heInt n)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun i => by dsimp [e]; ring
  simpa only [heq,add_zero] using hfixed.add heConv

end OptimalG.Variational
