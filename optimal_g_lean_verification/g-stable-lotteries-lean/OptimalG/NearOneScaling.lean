import OptimalG.SigmaIntegralBounds

/-! The near-one reduction uses monotonicity of the actual normalized slack
integral, not a separately assumed interval estimate. -/
namespace OptimalG
open Set MeasureTheory

/-- For a nonnegative decreasing score, the integral divided by h² decreases
with h. The proof compares two adjacent intervals against their shared score. -/
theorem sigma_normalized_integral_antitone {sigma : ℝ → ℝ} {q H : ℝ}
    (hc : ContinuousOn sigma (Icc q (q+H)))
    (hn : ∀ r ∈ Icc q (q+H),0≤sigma r)
    (ha : AntitoneOn sigma (Icc q (q+H))) :
    AntitoneOn (fun h => (∫ r in q..q+h,sigma r)/h^2) (Ioc 0 H) := by
  intro a haI b hbI hab
  have hqa : q≤q+a := by linarith [haI.1]
  have hqb : q≤q+b := by linarith [hbI.1]
  have hqab : q+a≤q+b := by linarith
  have hca : ContinuousOn sigma (Icc q (q+a)) := hc.mono (Icc_subset_Icc le_rfl (by linarith [haI.2]))
  have hcb : ContinuousOn sigma (Icc (q+a) (q+b)) := hc.mono (Icc_subset_Icc (by linarith [haI.1]) (by linarith [hbI.2]))
  have hi1 := hca.intervalIntegrable_of_Icc (μ := volume) hqa
  have hi2 := hcb.intervalIntegrable_of_Icc (μ := volume) hqab
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hfirst : a*sigma (q+a)≤∫ r in q..q+a,sigma r := by
    have hh := intervalIntegral.integral_mono_on hqa
      (intervalIntegrable_const (c:=sigma (q+a))) hi1 (fun r hr =>
        ha ⟨hr.1,by linarith [hr.2,haI.2]⟩ ⟨hqa,by linarith [haI.2]⟩ hr.2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left] using hh
  have hsecond : (∫ r in q+a..q+b,sigma r)≤(b-a)*sigma (q+a) := by
    have hh := intervalIntegral.integral_mono_on hqab hi2
      (intervalIntegrable_const (c:=sigma (q+a))) (fun r hr =>
        ha ⟨hqa,by linarith [haI.2]⟩ ⟨by linarith [hr.1],by linarith [hr.2,hbI.2]⟩ hr.1)
    convert hh using 1 <;> simp only [intervalIntegral.integral_const,smul_eq_mul] <;> ring
  have hsplit' := congrArg (fun u : ℝ => a*u) hsplit
  have havg : a*(∫ r in q..q+b,sigma r)≤b*(∫ r in q..q+a,sigma r) := by
    have h1 := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hab)
    have h2 := mul_le_mul_of_nonneg_left hsecond haI.1.le
    nlinarith
  have hnon : 0≤∫ r in q..q+a,sigma r := intervalIntegral.integral_nonneg hqa
    (fun r hr => hn r ⟨hr.1,by linarith [hr.2,haI.2]⟩)
  apply (div_le_div_iff₀ (sq_pos_of_pos hbI.1) (sq_pos_of_pos haI.1)).mpr
  have h1 := mul_le_mul_of_nonneg_left havg haI.1.le
  have h2 := mul_nonneg (sub_nonneg.mpr hab)
    (mul_nonneg hbI.1.le hnon)
  nlinarith

/-- One stored near-one check and an upper bound for κ control every smaller
positive tail width. -/
theorem nearOne_test_of_endpoint {sigma : ℝ → ℝ} {q H h lam kappa upper : ℝ}
    (hc : ContinuousOn sigma (Icc q (q+H)))
    (hn : ∀ r ∈ Icc q (q+H),0≤sigma r)
    (ha : AntitoneOn sigma (Icc q (q+H)))
    (hh : h ∈ Ioc 0 H) (hql : q≤lam) (hk : kappa≤upper)
    (hend : 0≤(∫ r in q..q+H,sigma r)/H^2-upper*(lam-q)+1/2) :
    0≤(∫ r in q..q+h,sigma r)/h^2-kappa*(lam-q)+1/2 := by
  have havg := sigma_normalized_integral_antitone hc hn ha hh
    ⟨hh.1.trans_le hh.2,le_rfl⟩ hh.2
  have hm := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hql)
  linarith

/-- The exact C.18 normalization of the binary inequality. D is the actual
primitive increment once the slack-integral identity is substituted. -/
theorem nearOne_binary_iff_normalized {h lam q Jp D I : ℝ}
    (hh : 0<h) (hh1 : h<1)
    (hD : D=(lam-q)*h-h^2/2-I) :
    (1-h)*D≤(lam-q)*Jp ↔
      0≤I/h^2-((h-Jp/(1-h))/h^2)*(lam-q)+1/2 := by
  let F := I/h^2-((h-Jp/(1-h))/h^2)*(lam-q)+1/2
  have hp : 0<(1-h)*h^2 := mul_pos (sub_pos.mpr hh1) (sq_pos_of_pos hh)
  have hid : ((1-h)*h^2)*F=(lam-q)*Jp-(1-h)*D := by
    dsimp [F]
    rw [hD]
    field_simp [hh.ne',(sub_pos.mpr hh1).ne']
    ring
  constructor
  · intro htest
    have hm : 0≤((1-h)*h^2)*F := by rw [hid]; exact sub_nonneg.mpr htest
    exact nonneg_of_mul_nonneg_right hm hp
  · intro htest
    have hm := mul_nonneg hp.le htest
    change 0≤((1-h)*h^2)*F at hm
    rw [hid] at hm
    exact sub_nonneg.mp hm

end OptimalG
