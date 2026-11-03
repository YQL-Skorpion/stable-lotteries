import OptimalG.VariationalStrongControl

/-! Uniform control perturbation bounds along a fixed continuous state path. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

private theorem polynomial_error_bound (a b c d z u ea eb ec ed C : ℝ)
    (ha : |a| ≤ ea) (hb : |b| ≤ eb) (hc : |c| ≤ ec) (hd : |d| ≤ ed)
    (hC : 0 ≤ C) (hz : |z| ≤ 1) (hu : |u| ≤ C) :
    |a*z^2+b*z+c*u+d| ≤ ea+eb+ec*C+ed := by
  have hza : |z^2| ≤ 1 := by rw [abs_pow]; nlinarith [abs_nonneg z]
  have hea : 0 ≤ ea := (abs_nonneg _).trans ha
  have heb : 0 ≤ eb := (abs_nonneg _).trans hb
  have hec : 0 ≤ ec := (abs_nonneg _).trans hc
  have h1 : |a*z^2| ≤ ea := by
    rw [abs_mul]
    exact (mul_le_mul ha hza (abs_nonneg _) hea).trans_eq (mul_one _)
  have h2 : |b*z| ≤ eb := by
    rw [abs_mul]
    exact (mul_le_mul hb hz (abs_nonneg _) heb).trans_eq (mul_one _)
  have h3 : |c*u| ≤ ec*C := by rw [abs_mul]; exact mul_le_mul hc hu (abs_nonneg _) hec
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add h1 h2)) h3)) hd)

/-- The error bound is uniform in time outside one null set of controls.
This stronger form permits a fixed-gap argument at all near-active controls. -/
theorem controlH_uniform_path_error
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (hphi : AENormTendsto (fun n => (dn n).phi) d.phi (volume.restrict (Icc ell tEnd)))
    (Y : ℝ → ℝ) (hY : ContinuousOn Y (Icc zStart zEnd))
    (qn : ℕ → ℝ) (hq : Tendsto qn atTop (𝓝 0)) :
    ∃ en : ℕ → ℝ, Tendsto en atTop (𝓝 0) ∧ ∀ n, 0 ≤ en n ∧
      ∀ᵐ c ∂controlMeasure, ∀ z ∈ Icc zStart zEnd,
        |controlH (lamn n) (dn n) z (Y z+qn n) c-controlH lam d z (Y z) c| ≤ en n := by
  let Hn := fun n a b c => controlH (lamn n) (dn n) a b c
  let H := fun a b c => controlH lam d a b c
  have h0 := (controlH_AENormTendsto lamn dn hn hd hlam hS hJ hphi 0 0).converges
  have hp := (controlH_AENormTendsto lamn dn hn hd hlam hS hJ hphi 1 0).converges
  have hm := (controlH_AENormTendsto lamn dn hn hd hlam hS hJ hphi (-1) 0).converges
  have h1 := (controlH_AENormTendsto lamn dn hn hd hlam hS hJ hphi 0 1).converges
  obtain ⟨ea, hea, hba⟩ := ((hp.add hm).sub (h0.const_mul 2)).div_const 2
  obtain ⟨eb, heb, hbb⟩ := (hp.sub hm).div_const 2
  obtain ⟨ec, hec, hbc⟩ := h1.sub h0
  obtain ⟨ed, hed, hbd⟩ := h0
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hYB : ∀ z ∈ Icc zStart zEnd, |Y z| ≤ C := fun z hz => (hC0 z hz).trans (le_max_left _ _)
  refine ⟨fun n => ea n+eb n+ec n*C+ed n+(19/2)*|qn n|, ?_, fun n => ⟨?_, ?_⟩⟩
  · simpa using (((hea.add heb).add (hec.mul_const C)).add hed).add (hq.abs.const_mul (19/2))
  · have := (hba n).1
    have := (hbb n).1
    have := (hbc n).1
    have := (hbd n).1
    positivity
  · filter_upwards [(hba n).2, (hbb n).2, (hbc n).2, (hbd n).2, (hn n).controlAlpha_bound]
      with c hac hbc' hcc hdc hAc
    intro z hz
    have hzabs : |z| ≤ 1 := by
      have hzl := hz.1
      have hzu := hz.2
      norm_num [zStart, zEnd] at hzl hzu
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hpoly := polynomial_error_bound
      (((Hn n 1 0 c+Hn n (-1) 0 c-2*Hn n 0 0 c)/2)-((H 1 0 c+H (-1) 0 c-2*H 0 0 c)/2))
      (((Hn n 1 0 c-Hn n (-1) 0 c)/2)-((H 1 0 c-H (-1) 0 c)/2))
      ((Hn n 0 1 c-Hn n 0 0 c)-(H 0 1 c-H 0 0 c)) (Hn n 0 0 c-H 0 0 c)
      z (Y z) (ea n) (eb n) (ec n) (ed n) C hac hbc' hcc hdc hC hzabs (hYB z hz)
    have heq : controlH (lamn n) (dn n) z (Y z) c-controlH lam d z (Y z) c =
        (((Hn n 1 0 c+Hn n (-1) 0 c-2*Hn n 0 0 c)/2)-((H 1 0 c+H (-1) 0 c-2*H 0 0 c)/2))*z^2+
        (((Hn n 1 0 c-Hn n (-1) 0 c)/2)-((H 1 0 c-H (-1) 0 c)/2))*z+
        ((Hn n 0 1 c-Hn n 0 0 c)-(H 0 1 c-H 0 0 c))*Y z+(Hn n 0 0 c-H 0 0 c) := by
      rw [controlH_quadratic_interpolation (lamn n) (dn n) z (Y z) c,
        controlH_quadratic_interpolation lam d z (Y z) c]
      dsimp [Hn, H]
      ring
    rw [← heq] at hpoly
    have hshift : controlH (lamn n) (dn n) z (Y z+qn n) c =
        controlH (lamn n) (dn n) z (Y z) c+controlAlpha (lamn n) (dn n) c*qn n := by
      rw [controlH_affine (lamn n) (dn n) z (Y z+qn n) c,
        controlH_affine (lamn n) (dn n) z (Y z) c]
      ring
    rw [hshift]
    have hab := (abs_mul (controlAlpha (lamn n) (dn n) c) (qn n)).le.trans
      (mul_le_mul_of_nonneg_right hAc (abs_nonneg _))
    have htri := abs_add_le
      (controlH (lamn n) (dn n) z (Y z) c-controlH lam d z (Y z) c)
      (controlAlpha (lamn n) (dn n) c*qn n)
    have heq' : controlH (lamn n) (dn n) z (Y z) c+controlAlpha (lamn n) (dn n) c*qn n-
        controlH lam d z (Y z) c =
        (controlH (lamn n) (dn n) z (Y z) c-controlH lam d z (Y z) c)+
          controlAlpha (lamn n) (dn n) c*qn n := by ring
    rw [heq']
    exact htri.trans (add_le_add hpoly hab)

end OptimalG.Variational
