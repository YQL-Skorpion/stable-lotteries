import OptimalG.VariationalODE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Quantitative stability of scalar ODEs under integrable residual errors. -/

namespace OptimalG.Variational

open Set Real MeasureTheory Filter
open scoped NNReal Topology

/-- An exponential-integral barrier controls both signs of the trajectory error. -/
theorem scalar_ode_l1_gap_of_continuous
    (G : ℝ → ℝ → ℝ) (K : ℝ≥0) (x y xd r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : ∀ t ∈ Ico a b, LipschitzWith K (G t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (xd t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (G t (y t)) (Ici t) t)
    (hr : Continuous r) (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hres : ∀ t ∈ Ico a b, |G t (x t)-xd t| ≤ r t) :
    ∀ t ∈ Icc a b, |y t-x t| ≤
      exp ((K:ℝ)*(b-a))*(|y a-x a|+∫ s in a..b, r s) := by
  let e : ℝ → ℝ := fun t => exp ((K:ℝ)*(t-a))*(|y a-x a|+∫ s in a..t, r s)
  have hdexp (t : ℝ) : HasDerivAt (fun s : ℝ => exp ((K:ℝ)*(s-a)))
      ((K:ℝ)*exp ((K:ℝ)*(t-a))) t := by
    simpa only [id_eq, mul_one, mul_comm] using (((hasDerivAt_id t).sub_const a).const_mul (K:ℝ)).exp
  have hdint (t : ℝ) : HasDerivAt (fun t => ∫ s in a..t, r s) (r t) t :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable a t)
      (hr.stronglyMeasurableAtFilter volume (𝓝 t)) hr.continuousAt
  have hed (t : ℝ) : HasDerivAt e ((K:ℝ)*e t+exp ((K:ℝ)*(t-a))*r t) t := by
    have hh := (hdexp t).mul ((hdint t).const_add |y a-x a|)
    change HasDerivAt e
      (((K:ℝ)*exp ((K:ℝ)*(t-a)))*(|y a-x a|+∫ s in a..t,r s)+exp ((K:ℝ)*(t-a))*r t) t at hh
    have he : ((K:ℝ)*exp ((K:ℝ)*(t-a)))*(|y a-x a|+∫ s in a..t,r s)+exp ((K:ℝ)*(t-a))*r t =
        (K:ℝ)*e t+exp ((K:ℝ)*(t-a))*r t := by dsimp [e]; ring
    rwa [he] at hh
  have hecont : Continuous e := continuous_iff_continuousAt.mpr fun t => (hed t).continuousAt
  have he0 : e a = |y a-x a| := by simp [e]
  have hepos {t : ℝ} (ht : t ∈ Icc a b) : 0 ≤ e t := by
    have hi := intervalIntegral.integral_nonneg (μ:=volume) ht.1 (fun s hs => hr0 s ⟨hs.1,hs.2.trans ht.2⟩)
    exact mul_nonneg (le_of_lt (exp_pos _)) (add_nonneg (abs_nonneg _) hi)
  have hedLower {t : ℝ} (ht : t ∈ Icc a b) :
      (K:ℝ)*e t+r t ≤ (K:ℝ)*e t+exp ((K:ℝ)*(t-a))*r t := by
    have hexp : 1 ≤ exp ((K:ℝ)*(t-a)) := one_le_exp (mul_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1))
    have hm := mul_le_mul_of_nonneg_right hexp (hr0 t ht)
    linarith
  have hupper := scalar_ode_comparison G K y (fun t => x t+e t)
    (fun t => G t (y t)) (fun t => xd t+((K:ℝ)*e t+exp ((K:ℝ)*(t-a))*r t)) a b
    hG hy (hx.add hecont.continuousOn) hyd
    (fun t ht => (hxd t ht).add (hed t).hasDerivWithinAt)
    (fun _ _ => le_rfl) (fun t ht => ?_) (by rw [he0]; linarith [le_abs_self (y a-x a)])
  · have hlower := scalar_ode_comparison G K (fun t => x t-e t) y
      (fun t => xd t-((K:ℝ)*e t+exp ((K:ℝ)*(t-a))*r t)) (fun t => G t (y t)) a b
      hG (hx.sub hecont.continuousOn) hy
      (fun t ht => (hxd t ht).sub (hed t).hasDerivWithinAt) hyd
      (fun t ht => ?_) (fun _ _ => le_rfl) (by rw [he0]; linarith [neg_abs_le (y a-x a)])
    · intro t ht
      have hgap : |y t-x t| ≤ e t := abs_le.mpr ⟨by linarith [hlower t ht],by linarith [hupper t ht]⟩
      have hri : 0 ≤ᵐ[volume.restrict (Ioc a b)] r := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hr0 s ⟨le_of_lt hs.1,hs.2⟩
      have hint := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hri (hr.intervalIntegrable a b)
      have hexp : exp ((K:ℝ)*(t-a)) ≤ exp ((K:ℝ)*(b-a)) :=
        exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) K.coe_nonneg)
      have hi0 := intervalIntegral.integral_nonneg (μ:=volume) ht.1 (fun s hs => hr0 s ⟨hs.1,hs.2.trans ht.2⟩)
      apply hgap.trans
      exact mul_le_mul hexp (add_le_add le_rfl hint)
        (add_nonneg (abs_nonneg _) hi0) (le_of_lt (exp_pos _))
    · have hlip := (hG t ht).dist_le_mul (x t-e t) (x t)
      rw [Real.dist_eq,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_nonneg (hepos ⟨ht.1,le_of_lt ht.2⟩)] at hlip
      have hdiff : -(K:ℝ)*e t ≤ G t (x t-e t)-G t (x t) := by
        linarith [neg_abs_le (G t (x t-e t)-G t (x t))]
      have hres' := (neg_abs_le (G t (x t)-xd t))
      have hb := hedLower ⟨ht.1,le_of_lt ht.2⟩
      linarith [hres t ht]
  · have hlip := (hG t ht).dist_le_mul (x t+e t) (x t)
    rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_nonneg (hepos ⟨ht.1,le_of_lt ht.2⟩)] at hlip
    have hdiff := (le_abs_self (G t (x t+e t)-G t (x t))).trans hlip
    have hres' := (le_abs_self (G t (x t)-xd t)).trans (hres t ht)
    have hb := hedLower ⟨ht.1,le_of_lt ht.2⟩
    linarith

/-- Only continuity on the time interval is needed. Outside values are removed
by a continuous clamped extension before applying the barrier argument. -/
theorem scalar_ode_l1_gap
    (G : ℝ → ℝ → ℝ) (K : ℝ≥0) (x y xd r : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : ∀ t ∈ Ico a b, LipschitzWith K (G t))
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (xd t) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (G t (y t)) (Ici t) t)
    (hr : ContinuousOn r (Icc a b)) (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hres : ∀ t ∈ Ico a b, |G t (x t)-xd t| ≤ r t) :
    ∀ t ∈ Icc a b, |y t-x t| ≤
      exp ((K:ℝ)*(b-a))*(|y a-x a|+∫ s in a..b, r s) := by
  let R : ℝ → ℝ := IccExtend hab (fun t : Icc a b => r t)
  have hRc : Continuous R := (continuousOn_iff_continuous_restrict.mp hr).Icc_extend'
  have hReq (t : ℝ) (ht : t ∈ Icc a b) : R t=r t := IccExtend_of_mem hab _ ht
  have hRi : (∫ s in a..b, R s) = ∫ s in a..b, r s := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hReq t (by simpa only [uIcc_of_le hab] using ht)
  have hh := scalar_ode_l1_gap_of_continuous G K x y xd R a b hab hG hx hy hxd hyd hRc
    (fun t ht => by rw [hReq t ht]; exact hr0 t ht)
    (fun t ht => by rw [hReq t ⟨ht.1,le_of_lt ht.2⟩]; exact hres t ht)
  simpa only [hRi] using hh

/-- A common state Lipschitz constant and vanishing L¹ residuals imply uniform
convergence of trajectories; pointwise convergence of derivatives is unnecessary. -/
theorem scalar_ode_tendstoUniformlyOn_of_l1_residual
    (G : ℕ → ℝ → ℝ → ℝ) (K : ℝ≥0) (xn : ℕ → ℝ → ℝ) (x xd : ℝ → ℝ)
    (r : ℕ → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : ∀ n t, t ∈ Ico a b → LipschitzWith K (G n t))
    (hx : ContinuousOn x (Icc a b)) (hxn : ∀ n, ContinuousOn (xn n) (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (xd t) (Ici t) t)
    (hxnd : ∀ n t, t ∈ Ico a b → HasDerivWithinAt (xn n) (G n t (xn n t)) (Ici t) t)
    (hr : ∀ n, ContinuousOn (r n) (Icc a b)) (hr0 : ∀ n t, t ∈ Icc a b → 0 ≤ r n t)
    (hres : ∀ n t, t ∈ Ico a b → |G n t (x t)-xd t| ≤ r n t)
    (hinit : Tendsto (fun n => xn n a) atTop (𝓝 (x a)))
    (herror : Tendsto (fun n => ∫ t in a..b, r n t) atTop (𝓝 0)) :
    TendstoUniformlyOn xn x atTop (Icc a b) := by
  have hb : Tendsto (fun n => exp ((K:ℝ)*(b-a))*(|xn n a-x a|+∫ t in a..b,r n t))
      atTop (𝓝 0) := by
    simpa using ((hinit.sub (tendsto_const_nhds (x:=x a))).abs.add herror).const_mul
      (exp ((K:ℝ)*(b-a)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  filter_upwards [(tendsto_order.mp hb).2 eps heps] with n hn
  intro t ht
  have hgap := scalar_ode_l1_gap (G n) K x (xn n) xd (r n) a b hab (hG n)
    hx (hxn n) hxd (hxnd n) (hr n) (hr0 n) (hres n) t ht
  rw [Real.dist_eq,abs_sub_comm]
  exact hgap.trans_lt hn

/-- Direct specialization to exact solutions of converging vector fields. -/
theorem scalar_ode_solutions_tendstoUniformlyOn
    (Gn : ℕ → ℝ → ℝ → ℝ) (F : ℝ → ℝ → ℝ) (K : ℝ≥0)
    (xn : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : ∀ n t, t ∈ Ico a b → LipschitzWith K (Gn n t))
    (hx : ContinuousOn x (Icc a b)) (hxn : ∀ n, ContinuousOn (xn n) (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hxnd : ∀ n t, t ∈ Ico a b → HasDerivWithinAt (xn n) (Gn n t (xn n t)) (Ici t) t)
    (hr : ∀ n, ContinuousOn (fun t => |Gn n t (x t)-F t (x t)|) (Icc a b))
    (hinit : Tendsto (fun n => xn n a) atTop (𝓝 (x a)))
    (herror : Tendsto (fun n => ∫ t in a..b, |Gn n t (x t)-F t (x t)|) atTop (𝓝 0)) :
    TendstoUniformlyOn xn x atTop (Icc a b) :=
  scalar_ode_tendstoUniformlyOn_of_l1_residual Gn K xn x (fun t => F t (x t))
    (fun n t => |Gn n t (x t)-F t (x t)|) a b hab hG hx hxn hxd hxnd hr
    (fun _ _ _ => abs_nonneg _) (fun _ _ _ => le_rfl) hinit herror

end OptimalG.Variational
