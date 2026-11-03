import OptimalG.Certificates.HighAssembly
import OptimalG.VariationalAffineComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Actual affine reference flows are enclosed by checked C¹ polynomial
approximations. The initial value is exact; all error comes from the proved
residual bound, not from a numerical ODE solver. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

theorem absolutelyContinuous_of_continuous_derivative {X X' : ℝ→ℝ}
    (hd : ∀ t,HasDerivAt X (X' t) t) (hc : Continuous X') (a b : ℝ) :
    AbsolutelyContinuousOnInterval X a b := by
  have he : deriv X=X' := funext (fun t => (hd t).deriv)
  have h : ContDiff ℝ 1 X := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hd t).differentiableAt,by rwa [he]⟩
  exact h.contDiffOn.absolutelyContinuousOnInterval

theorem trajectoryCheck_absolutelyContinuous (L S : ℚ) (ps : List CubicPiece)
    (hc : trajectoryCheck L S ps=true) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (cubicPrimitive L S ps) a b :=
  absolutelyContinuous_of_continuous_derivative
    (trajectoryCheck_hasDerivAt L S ps hc) (trajectoryCheck_continuousScore L S ps hc) a b

theorem affine_flow_enclosed_by_residual {a b A eta delta : ℝ}
    {alpha beta X X' Z : ℝ→ℝ}
    (hA : 0≤A) (hdelta : 0≤delta)
    (hbudget : eta≤delta*(1-A*(b-a)))
    (ha : IntervalIntegrable alpha volume a b)
    (hXder : ∀ t,HasDerivAt X (X' t) t) (hXcont : Continuous X')
    (hZ : AbsolutelyContinuousOnInterval Z a b) (hinit : X a=Z a)
    (hZd : ∀ᵐ t ∂volume.restrict (Icc a b),deriv Z t=alpha t*Z t+beta t)
    (hAlpha : ∀ᵐ t ∂volume.restrict (Icc a b),alpha t≤A)
    (hResidual : ∀ᵐ t ∂volume.restrict (Icc a b),|X' t-alpha t*X t-beta t|≤eta) :
    ∀ t∈Icc a b,|Z t-X t|≤delta*(t-a) := by
  have hX := absolutelyContinuous_of_continuous_derivative hXder hXcont a b
  have htilt : AbsolutelyContinuousOnInterval (fun t : ℝ => delta*(t-a)) a b :=
    (show ContDiff ℝ 1 (fun t : ℝ => delta*(t-a)) from
      contDiff_const.mul (contDiff_id.sub contDiff_const)).contDiffOn.absolutelyContinuousOnInterval
  have htder (t : ℝ) : HasDerivAt (fun t : ℝ => delta*(t-a)) delta t := by
    convert! ((hasDerivAt_id t).sub_const a).const_mul delta using 1 <;>
      first | rfl | simp
  have hmargin : ∀ᵐ t ∂volume.restrict (Icc a b),
      eta≤delta*(1-alpha t*(t-a)) := by
    filter_upwards [hAlpha,self_mem_ae_restrict measurableSet_Icc] with t ht hmem
    have hmul := mul_le_mul_of_nonneg_right ht (sub_nonneg.mpr hmem.1)
    have htime := mul_le_mul_of_nonneg_left (show t-a≤b-a by linarith [hmem.2]) hA
    have hd := mul_le_mul_of_nonneg_left (show 1-A*(b-a)≤1-alpha t*(t-a) by linarith) hdelta
    exact hbudget.trans hd
  have hlo := Variational.integrable_affine_ode_comparison ha (hX.sub htilt) hZ
    (by simpa using hinit.le)
    (by
      filter_upwards [hResidual,hmargin] with t hr hm
      rw [((hXder t).sub (htder t)).deriv]
      have hh := (abs_le.mp hr).2
      dsimp
      nlinarith only [hh,hm]) (hZd.mono fun _ h => h.ge)
  have hhi := Variational.integrable_affine_ode_comparison ha hZ (hX.add htilt)
    (by simpa using hinit.ge) (hZd.mono fun _ h => h.le)
    (by
      filter_upwards [hResidual,hmargin] with t hr hm
      rw [((hXder t).add (htder t)).deriv]
      have hh := (abs_le.mp hr).1
      dsimp
      nlinarith only [hh,hm])
  intro t ht
  have hl := hlo t ht
  have hu := hhi t ht
  apply abs_le.mpr
  constructor <;> dsimp at hl hu <;> linarith

/-- Common exact constants used for both endpoint-reference flows. -/
theorem reference_flow_enclosed {a b : ℝ} {alpha beta X X' Z : ℝ→ℝ}
    (hlen : b-a≤2/25)
    (ha : IntervalIntegrable alpha volume a b)
    (hXder : ∀ t,HasDerivAt X (X' t) t) (hXcont : Continuous X')
    (hZ : AbsolutelyContinuousOnInterval Z a b) (hinit : X a=Z a)
    (hZd : ∀ᵐ t ∂volume.restrict (Icc a b),deriv Z t=alpha t*Z t+beta t)
    (hAlpha : ∀ᵐ t ∂volume.restrict (Icc a b),alpha t≤3)
    (hResidual : ∀ᵐ t ∂volume.restrict (Icc a b),
      |X' t-alpha t*X t-beta t|≤1/4000000000) :
    ∀ t∈Icc a b,|Z t-X t|≤(t-a)/2500000000 := by
  have h := affine_flow_enclosed_by_residual (A:=3) (delta:=1/2500000000)
    (by norm_num) (by norm_num) (by nlinarith) ha hXder hXcont hZ hinit hZd hAlpha hResidual
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using h

end OptimalG.Certificates.Transport
