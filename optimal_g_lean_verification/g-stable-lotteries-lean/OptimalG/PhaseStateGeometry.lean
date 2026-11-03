import OptimalG.UniversalPhaseBoxes
import OptimalG.PhasePropagation

/-! All interpolated states stay in the required K-box before ODE comparison.
The proof uses monotonic retained slack and the explicit candidate error. -/
namespace OptimalG
open Set

noncomputable def mixedSlack (S T : ℝ → ℝ) (t r : ℝ) : ℝ := (1-t)*S r+t*T r

theorem mixedSlack_monotone {S T : ℝ → ℝ} (hS : Monotone S) (hT : Monotone T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : Monotone (mixedSlack S T t) := by
  intro a b hab
  exact add_le_add (mul_le_mul_of_nonneg_left (hS hab) (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left (hT hab) ht.1)

theorem mixedSlack_nonneg {S T : ℝ → ℝ} {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hS : 0 ≤ S r) (hT : 0 ≤ T r) :
    0 ≤ mixedSlack S T t r :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hS) (mul_nonneg ht.1 hT)

theorem mixedSlack_start {S T : ℝ → ℝ} {t a gain : ℝ} (h : T a = S a-gain) :
    mixedSlack S T t a = S a-t*gain := by
  unfold mixedSlack
  rw [h]
  ring

/-- The candidate state and interpolated primitive have positive gap K,
without assuming the new ODE solution already stays in a numerical box. -/
theorem interpolated_phase_gap {lam p z Y t gain err : ℝ} {S T : ℝ → ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hp : p ∈ Icc (0.25 : ℝ) 0.36) (hz : z ∈ Icc (0.775 : ℝ) 0.875)
    (ht : t ∈ Icc (0 : ℝ) 1) (hS : Monotone S) (hT : Monotone T)
    (hSn : 0 ≤ S (z-p)) (hTn : 0 ≤ T (z-p))
    (hstart : T 0.775=S 0.775-gain)
    (hYlow : linePrimitive lam z-linePrimitive lam 1 ≤ Y)
    (hYhi : Y ≤ linePrimitive lam z-S 0.775)
    (he : 0 ≤ err) (hgain : err ≤ gain) :
    let Jm := linePrimitive lam (z-p)-mixedSlack S T t (z-p)
    let U := Y+t*(gain-err)
    linePrimitive lam z-linePrimitive lam 1 ≤ U ∧
    U ≤ linePrimitive lam z-mixedSlack S T t 0.775 ∧
    0 < Jm-U ∧ Jm-U < 0.111315 := by
  have hm := mixedSlack_monotone hS hT ht
    (show z-p ≤ (0.775 : ℝ) by linarith [hz.2,hp.1])
  have hn := mixedSlack_nonneg ht hSn hTn
  have hs := mixedSlack_start (t := t) hstart
  have hte := mul_nonneg ht.1 he
  have htg := mul_nonneg ht.1 (sub_nonneg.mpr hgain)
  have hl : linePrimitive lam z-linePrimitive lam 1 ≤ Y+t*(gain-err) := by linarith
  have hh : Y+t*(gain-err) ≤ linePrimitive lam z-mixedSlack S T t 0.775 := by
    rw [hs]
    nlinarith only [hYhi,hte]
  have hceiling : (Y+t*(gain-err))-(linePrimitive lam (z-p)-mixedSlack S T t (z-p)) ≤
      lam*p-(z^2-(z-p)^2)/2 := by
    unfold linePrimitive at hh ⊢
    nlinarith only [hh,hm]
  have hgap := continuation_gap_bounds hL hp hz
    (show linePrimitive lam (z-p)-mixedSlack S T t (z-p) ≤ linePrimitive lam (z-p) by linarith)
    hl hceiling
  exact ⟨hl,hh,hgap⟩

end OptimalG
