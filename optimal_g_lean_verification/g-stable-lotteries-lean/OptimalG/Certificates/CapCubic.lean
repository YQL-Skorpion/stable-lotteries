import OptimalG.Certificates.CubicBounds
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Attaching the analytic cap prefix to a certified cubic primitive. -/
namespace OptimalG.Certificates
open Set Filter
open scoped Topology

noncomputable def capSlope (L S r : ℝ) : ℝ := L/2-L*S/(1-r)^2

theorem cap_hasDerivAt (L S r : ℝ) (hr : r≠1) :
    HasDerivAt (cap L S) (capSlope L S r) r := by
  have hh : 1-r≠0 := sub_ne_zero.mpr (Ne.symm hr)
  have hi := hasDerivAt_id r
  have hd := (((hi.const_mul L).div_const 2).const_add (L^2-L/2)).sub
    ((hasDerivAt_const r (L*S)).div ((hasDerivAt_const r 1).sub hi) hh)
  have he : L*1/2-(0*(1-r)-L*S*(0-1))/(1-r)^2=capSlope L S r := by simp [capSlope]
  change HasDerivAt (cap L S) (L*1/2-(0*(1-r)-L*S*(0-1))/(1-r)^2) r at hd
  rwa [he] at hd

/-- Only the derivative on the selected side is required for the prefix. -/
theorem hasDerivAt_glue_le_of_left (a : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ x≤a, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hv : f a=g a) (hd : df a=dg a) (x : ℝ) :
    HasDerivAt (fun t => if t≤a then f t else g t) (if x≤a then df x else dg x) x := by
  rcases lt_trichotomy x a with hx | heq | hx
  · rw [if_pos (le_of_lt hx)]
    apply (hf x (le_of_lt hx)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with t ht
    exact if_pos (le_of_lt ht)
  · subst x
    rw [if_pos le_rfl]
    have hl : HasDerivWithinAt (fun t => if t≤a then f t else g t) (df a) (Iic a) a :=
      (hf a le_rfl).hasDerivWithinAt.congr (fun t ht => if_pos ht) (if_pos le_rfl)
    have hr : HasDerivWithinAt (fun t => if t≤a then f t else g t) (df a) (Ioi a) a := by
      apply ((hg a).hasDerivWithinAt.congr_deriv hd.symm).congr
      · intro t ht
        exact if_neg (not_le_of_gt ht)
      · simpa only [if_pos le_rfl] using hv
    simpa only [Iic_union_Ioi,hasDerivWithinAt_univ] using hl.union hr
  · rw [if_neg (not_le_of_gt hx)]
    apply (hg x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact if_neg (not_le_of_gt ht)

noncomputable def capCubicScore (L S c : ℝ) (ps : List CubicPiece) (r : ℝ) : ℝ :=
  if r≤c then capSlope L S r else cubicScore L ps r

noncomputable def capCubicPrimitive (L S c : ℝ) (ps : List CubicPiece) (r : ℝ) : ℝ :=
  if r≤c then cap L S r else cubicPrimitive L S ps r

theorem capCubic_hasDerivAt {L S : ℚ} {c : ℝ} {ps : List CubicPiece}
    (hc : c<1) (ha : cubicAssemblyCheck L S ps=true)
    (hv : cap L S c=cubicPrimitive L S ps c)
    (hd : capSlope L S c=cubicScore L ps c) (r : ℝ) :
    HasDerivAt (capCubicPrimitive L S c ps) (capCubicScore L S c ps r) r := by
  apply hasDerivAt_glue_le_of_left c (cap L S) (cubicPrimitive L S ps)
    (capSlope L S) (cubicScore L ps) ?_ (cubicAssemblyCheck_hasDerivAt L S ps ha) hv hd
  intro x hx
  exact cap_hasDerivAt L S x (ne_of_lt (lt_of_le_of_lt hx hc))

theorem capCubic_continuousScore {L S : ℚ} {c : ℝ} {ps : List CubicPiece}
    (hc : c<1) (ha : cubicAssemblyCheck L S ps=true)
    (hd : capSlope L S c=cubicScore L ps c) : Continuous (capCubicScore L S c ps) := by
  have hmin : Continuous (fun r:ℝ => min r c) := continuous_id.min continuous_const
  have hn : ∀ r:ℝ, (1-min r c)^2≠0 := fun r =>
    pow_ne_zero _ (ne_of_gt (sub_pos.mpr (lt_of_le_of_lt (min_le_right r c) hc)))
  have hp : Continuous (fun r:ℝ => capSlope L S (min r c)) := by
    unfold capSlope
    exact continuous_const.sub (continuous_const.div ((continuous_const.sub hmin).pow 2) hn)
  have h := hp.if_le (cubicAssemblyCheck_continuousScore L S ps ha)
    continuous_id continuous_const (fun r hr => by
      change r=c at hr
      subst r
      simpa only [min_self] using hd)
  convert h using 1
  funext r
  by_cases hr : r≤c
  · simp only [capCubicScore,id_eq,if_pos hr,min_eq_left hr]
  · simp only [capCubicScore,id_eq,if_neg hr]

/-- Coarse exact bounds suffice on the short cap prefix; no floating point
approximation or sampling is used. -/
theorem capSlope_bounds {L S r : ℝ}
    (hL : L∈Icc (0.562:ℝ) 0.563) (hS : S∈Icc (0.023:ℝ) 0.024)
    (hr : r∈Icc (0.28:ℝ) 0.296) : 0≤capSlope L S r ∧ capSlope L S r≤L-r := by
  have hdlo : (0.704:ℝ)^2≤(1-r)^2 := by nlinarith [hr.1,hr.2]
  have hdhi : (1-r)^2≤(0.72:ℝ)^2 := by nlinarith [hr.1,hr.2]
  have hd : 0<(1-r)^2 := lt_of_lt_of_le (by norm_num) hdlo
  have hnlo : (0.562:ℝ)*0.023≤L*S :=
    mul_le_mul hL.1 hS.1 (by norm_num) (by linarith [hL.1])
  have hnhi : L*S≤(0.563:ℝ)*0.024 :=
    mul_le_mul hL.2 hS.2 (by linarith [hS.1]) (by norm_num)
  have hqlo : (0.02:ℝ)≤L*S/(1-r)^2 := by
    apply (le_div_iff₀ hd).mpr
    nlinarith
  have hqhi : L*S/(1-r)^2≤(0.03:ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith
  unfold capSlope
  constructor <;> linarith [hL.1,hr.2]

end OptimalG.Certificates
