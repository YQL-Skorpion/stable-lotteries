import OptimalG.VariationalRecovery
import Mathlib.Analysis.Convex.Deriv

/-! Shape of a continuation from its attained differential controls.  The
argument uses primitive increments, so no second derivative is assumed. -/
namespace OptimalG
open Set

noncomputable def highAffineControl (lam S p theta alpha : ℝ) (J : ℝ → ℝ) (r : ℝ) : ℝ :=
  -theta*(r-lam)-alpha*(Variational.quadratic lam (r-p)-S-J r)

theorem highAffineControl_increment {lam S p theta alpha gamma a b : ℝ} {J : ℝ → ℝ}
    (hab : a ≤ b) (ha : 0 ≤ alpha) (hcoef : 1+gamma ≤ theta+alpha*p)
    (hinc : J b-J a ≤ Variational.quadratic lam b-Variational.quadratic lam a) :
    highAffineControl lam S p theta alpha J b-highAffineControl lam S p theta alpha J a ≤
      -(1+gamma)*(b-a) := by
  have hm := mul_le_mul_of_nonneg_left hinc ha
  have hc := mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hab)
  unfold highAffineControl Variational.quadratic at *
  nlinarith only [hm,hc]

/-- A pointwise attained lower envelope inherits a common upper slope bound. -/
theorem attained_envelope_upper_slope {ι : Type*} {s : Set ℝ} {f : ℝ → ℝ}
    {H : ι → ℝ → ℝ} {lam : ℝ}
    (hbound : ∀ r ∈ s, f r ≤ lam-r ∧ ∀ i, f r ≤ H i r)
    (hactive : ∀ r ∈ s, f r=lam-r ∨ ∃ i,f r=H i r)
    (hfall : ∀ i,∀ a ∈ s, ∀ b ∈ s, a ≤ b → H i b-H i a ≤ a-b) :
    ∀ a ∈ s, ∀ b ∈ s, a ≤ b → f b-f a ≤ a-b := by
  intro a ha b hb hab
  rcases hactive a ha with hl | ⟨i,hi⟩
  · linarith [(hbound b hb).1]
  · linarith [(hbound b hb).2 i,hfall i a ha b hb hab]

/-- A pointwise attained lower envelope of concave functions is concave. -/
theorem concaveOn_of_attained_envelope {ι : Type*} {s : Set ℝ} {f : ℝ → ℝ}
    {H : ι → ℝ → ℝ} (hs : Convex ℝ s)
    (hbound : ∀ r ∈ s,∀ i,f r ≤ H i r)
    (hactive : ∀ r ∈ s,∃ i,f r=H i r)
    (hconcave : ∀ i,ConcaveOn ℝ s (H i)) : ConcaveOn ℝ s f := by
  refine ⟨hs,?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨i,hi⟩ := hactive (a • x+b • y) (hs hx hy ha hb hab)
  rw [hi]
  exact (add_le_add (smul_le_smul_of_nonneg_left (hbound x hx i) ha)
    (smul_le_smul_of_nonneg_left (hbound y hy i) hb)).trans
      ((hconcave i).2 hx hy ha hb hab)

theorem quadratic_corrected_primitive_concave {a b : ℝ} {J f : ℝ → ℝ}
    (hcont : ContinuousOn J (Icc a b))
    (hderiv : ∀ r ∈ Ioo a b,HasDerivAt J (f r) r)
    (hfall : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x ≤ y → f y-f x ≤ x-y) :
    ConcaveOn ℝ (Icc a b) (fun r => J r+r^2/2) := by
  have hd (r : ℝ) (hr : r ∈ interior (Icc a b)) :
      HasDerivAt (fun r => J r+r^2/2) (f r+r) r := by
    rw [interior_Icc] at hr
    convert! (hderiv r hr).add (((hasDerivAt_id r).pow 2).div_const 2) using 1 <;> first | rfl | (simp only [id_eq]; ring)
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc a b) (by fun_prop)
    (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hd x hx).deriv,(hd y hy).deriv]
  linarith [hfall x (interior_subset hx) y (interior_subset hy) hxy]

theorem highAffineControl_concave {a b lam S p theta alpha : ℝ} {J : ℝ → ℝ}
    (ha : 0 ≤ alpha)
    (hJ : ConcaveOn ℝ (Icc a b) (fun r => J r+r^2/2)) :
    ConcaveOn ℝ (Icc a b) (highAffineControl lam S p theta alpha J) := by
  have hlin : ConcaveOn ℝ (Icc a b) (fun r : ℝ =>
      (-theta-alpha*(lam+p))*r+(theta*lam+alpha*(lam*p+p^2/2+S))) := by
    refine ⟨convex_Icc a b,?_⟩
    intro x hx y hy u v hu hv huv
    simp only [smul_eq_mul]
    have he : u*(theta*lam+alpha*(lam*p+p^2/2+S))+
        v*(theta*lam+alpha*(lam*p+p^2/2+S))=
        theta*lam+alpha*(lam*p+p^2/2+S) := by
      rw [← add_mul,huv,one_mul]
    nlinarith only [he]
  have hh := (hJ.smul ha).add hlin
  apply hh.congr
  intro r hr
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,highAffineControl,Variational.quadratic]
  ring


/-- The actual continuation inherits concavity from its attained affine controls.
The primitive upper-increment bound follows from the line branch of the ODE. -/
theorem highContinuation_concave {ι : Type*} {a b lam S : ℝ} {J f : ℝ → ℝ}
    {p theta alpha : ι → ℝ}
    (hcont : ContinuousOn J (Icc a b))
    (hderiv : ∀ r ∈ Ioo a b,HasDerivAt J (f r) r)
    (hcoef : ∀ i,0 ≤ alpha i ∧ 1 ≤ theta i+alpha i*p i)
    (hbound : ∀ r ∈ Icc a b,f r ≤ lam-r ∧
      ∀ i,f r ≤ highAffineControl lam S (p i) (theta i) (alpha i) J r)
    (hactive : ∀ r ∈ Icc a b,f r=lam-r ∨
      ∃ i,f r=highAffineControl lam S (p i) (theta i) (alpha i) J r) :
    (∀ x ∈ Icc a b,∀ y ∈ Icc a b,x ≤ y → f y-f x ≤ x-y) ∧
      ConcaveOn ℝ (Icc a b) f := by
  have hd (r : ℝ) (hr : r ∈ interior (Icc a b)) :
      HasDerivAt (fun r => J r-Variational.quadratic lam r) (f r-(lam-r)) r := by
    rw [interior_Icc] at hr
    exact (hderiv r hr).sub (Variational.quadratic_hasDerivAt lam r)
  have hmono : AntitoneOn (fun r => J r-Variational.quadratic lam r) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (hcont.sub (by unfold Variational.quadratic; fun_prop))
      (fun r hr => (hd r hr).differentiableAt.differentiableWithinAt)
    intro r hr
    change deriv (fun r => J r-Variational.quadratic lam r) r ≤ 0
    rw [(hd r hr).deriv]
    exact sub_nonpos.mpr (hbound r (interior_subset hr)).1
  have hfall : ∀ x ∈ Icc a b,∀ y ∈ Icc a b,x ≤ y → f y-f x ≤ x-y := by
    apply attained_envelope_upper_slope hbound hactive
    intro i x hx y hy hxy
    have hh := highAffineControl_increment (S := S) (gamma := 0) hxy (hcoef i).1
      (by simpa only [add_zero] using (hcoef i).2)
      (show J y-J x ≤ Variational.quadratic lam y-Variational.quadratic lam x by
        linarith [hmono hx hy hxy])
    convert! hh using 1 <;> ring
  refine ⟨hfall,?_⟩
  have hJ := quadratic_corrected_primitive_concave hcont hderiv hfall
  let H : Option ι → ℝ → ℝ := fun i => match i with
    | none => fun r => lam-r
    | some i => highAffineControl lam S (p i) (theta i) (alpha i) J
  apply concaveOn_of_attained_envelope (H := H) (convex_Icc a b)
  · intro r hr i
    cases i with
    | none => exact (hbound r hr).1
    | some i => exact (hbound r hr).2 i
  · intro r hr
    rcases hactive r hr with he | ⟨i,hi⟩
    · exact ⟨none,he⟩
    · exact ⟨some i,hi⟩
  · intro i
    cases i with
    | none =>
      refine ⟨convex_Icc a b,?_⟩
      intro x hx y hy u v hu hv huv
      change u*(lam-x)+v*(lam-y) ≤ lam-(u*x+v*y)
      have he : u*lam+v*lam=lam := by rw [← add_mul,huv,one_mul]
      nlinarith only [he]
    | some i => exact highAffineControl_concave (hcoef i).1 hJ

end OptimalG
