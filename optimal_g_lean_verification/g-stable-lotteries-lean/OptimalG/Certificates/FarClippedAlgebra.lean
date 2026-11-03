import OptimalG.Certificates.HighMassData.FarClippedHead
import OptimalG.Certificates.HighMassData.FarClippedNoOverflow
import OptimalG.Certificates.HighMassData.FarClippedOverflow

/-! Three small polynomial inequalities replace the far-split interval tree.
The actual average-score bounds are supplied separately by integration. -/
namespace OptimalG.Certificates
open Set

noncomputable def farClippedEnvelope (h q x : ℝ) : ℝ :=
  (x-q)-(309/1000)*(527/2000-q)-(691/2000)*h+
    (691/2000)*(max (q+h-527/2000) 0)^2/h

theorem farClipped_head_identity (h v : ℝ) :
    HighMassData.FarClippedHead.numerator h 0 v=
      (1-67*h/20)*v-(1-h)*(691/1000)*(v-h/2) := by
  norm_num [HighMassData.FarClippedHead.numerator]
  <;> ring

theorem farClipped_noOverflow_identity (h q : ℝ) :
    HighMassData.FarClippedNoOverflow.numerator h q 0=
      2*(1-h)*(309/1000)*(527/2000-q)+(691/1000)*(1-h)*h-
        (47/10)*h*(9/25-q) := by
  norm_num [HighMassData.FarClippedNoOverflow.numerator]
  <;> ring

theorem farClipped_overflow_identity (h q : ℝ) :
    HighMassData.FarClippedOverflow.numerator h q 0=
      2*h*(1-h)*(309/1000)*(527/2000-q)+(691/1000)*(1-h)*h^2-
        (691/1000)*(1-h)*(q+h-527/2000)^2-(47/10)*h^2*(9/25-q) := by
  norm_num [HighMassData.FarClippedOverflow.numerator]
  <;> ring

theorem farClipped_head_bound {h v : ℝ}
    (hh : h∈Icc (0:ℝ) (3/25)) (hv : v∈Icc (9/50:ℝ) (527/2000)) :
    ((1-h)/(1-67*h/20))*((691/1000)*(v-h/2))≤v := by
  have hn := HighMassData.FarClippedHead.numerator_pos hh
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num) hv
  rw [farClipped_head_identity] at hn
  have hd : 0<1-67*h/20 := by linarith only [hh.2]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hn]

theorem farClipped_free_bound {h q x : ℝ}
    (hh : h∈Ioc (0:ℝ) (3/25)) (hq : q∈Icc (0:ℝ) (9/50)) (hx : x≤9/25) :
    ((1-h)/(1-67*h/20))*farClippedEnvelope h q x≤x-q := by
  have hd : 0<1-67*h/20 := by linarith only [hh.2]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  by_cases hover : q+h≤527/2000
  · have hn := HighMassData.FarClippedNoOverflow.numerator_pos ⟨hh.1.le,hh.2⟩ hq
      (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    rw [farClipped_noOverflow_identity] at hn
    have hxgap := mul_nonneg hh.1.le (sub_nonneg.mpr hx)
    unfold farClippedEnvelope
    rw [max_eq_right (by linarith only [hover])]
    norm_num
    nlinarith only [hn,hxgap]
  · have hh' : h∈Icc (167/2000:ℝ) (3/25) := ⟨by linarith only [hover,hq.2],hh.2⟩
    have hq' : q∈Icc (287/2000:ℝ) (9/50) := ⟨by linarith only [hover,hh.2],hq.2⟩
    have hn := HighMassData.FarClippedOverflow.numerator_pos hh' hq'
      (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    rw [farClipped_overflow_identity] at hn
    have he : 2*h*((x-q)*(1-67*h/20)-(1-h)*farClippedEnvelope h q x)=
        HighMassData.FarClippedOverflow.numerator h q 0+(47/10)*h^2*(9/25-x) := by
      rw [farClipped_overflow_identity]
      unfold farClippedEnvelope
      rw [max_eq_left (by linarith only [hover])]
      field_simp [hh.1.ne']
      ring
    have hxgap := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hx)
    have hnon : 0≤(x-q)*(1-67*h/20)-(1-h)*farClippedEnvelope h q x := by
      apply nonneg_of_mul_nonneg_right (a:=2*h) ?_ (by nlinarith only [hh.1])
      rw [he]
      rw [farClipped_overflow_identity]
      nlinarith only [hn,hxgap]
    linarith only [hnon]

end OptimalG.Certificates
