import OptimalG.EnvelopeRepair
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The actual running-maximum primitive used in the repaired B.1 reduction. -/
namespace OptimalG
open Set
open scoped NNReal Topology

noncomputable def runningEnvelope (f : ℝ → ℝ) (a floor x : ℝ) : ℝ :=
  max floor (sSup (f '' Icc a x))

theorem runningEnvelope_attainment {f : ℝ → ℝ} {a b floor x : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hx : x ∈ Icc a b) :
    ∃ u ∈ Icc a x, runningEnvelope f a floor x = max floor (f u) ∧
      ∀ v ∈ Icc a x, f v ≤ f u := by
  obtain ⟨u, hu, hmax, hbound⟩ := isCompact_Icc.exists_sSup_image_eq_and_ge
    (nonempty_Icc.mpr hx.1) (hc.mono (Icc_subset_Icc le_rfl hx.2))
  exact ⟨u, hu, congrArg (max floor) hmax, hbound⟩

theorem runningEnvelope_floor (f : ℝ → ℝ) (a floor x : ℝ) : floor ≤ runningEnvelope f a floor x :=
  le_max_left _ _

theorem runningEnvelope_dominates {f : ℝ → ℝ} {a b floor x u : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hx : x ∈ Icc a b) (hu : u ∈ Icc a x) :
    f u ≤ runningEnvelope f a floor x := by
  obtain ⟨v, hv, heq, hmax⟩ := runningEnvelope_attainment hc hx (floor := floor)
  rw [heq]
  exact (hmax u hu).trans (le_max_right _ _)

theorem runningEnvelope_le {f : ℝ → ℝ} {a b floor x B : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hx : x ∈ Icc a b)
    (hf : floor ≤ B) (hbound : ∀ u ∈ Icc a x, f u ≤ B) :
    runningEnvelope f a floor x ≤ B := by
  obtain ⟨v, hv, heq, _⟩ := runningEnvelope_attainment hc hx (floor := floor)
  rw [heq]
  exact max_le hf (hbound v hv)

theorem runningEnvelope_monotone {f : ℝ → ℝ} {a b floor : ℝ}
    (hc : ContinuousOn f (Icc a b)) : MonotoneOn (runningEnvelope f a floor) (Icc a b) := by
  intro x hx y hy hxy
  apply runningEnvelope_le hc hx (runningEnvelope_floor f a floor y)
  intro u hu
  exact runningEnvelope_dominates hc hy ⟨hu.1, hu.2.trans hxy⟩

/-- The running maximum preserves any upper increment bound supplied by a
nondecreasing primitive, even when the original function decreases. -/
theorem runningEnvelope_increment {f Q : ℝ → ℝ} {a b floor : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hQ : MonotoneOn Q (Icc a b))
    (hinc : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → f y - f x ≤ Q y - Q x)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    0 ≤ runningEnvelope f a floor y - runningEnvelope f a floor x ∧
      runningEnvelope f a floor y - runningEnvelope f a floor x ≤ Q y - Q x := by
  have hQxy := hQ hx hy hxy
  refine ⟨sub_nonneg.mpr (runningEnvelope_monotone hc hx hy hxy), ?_⟩
  have hb : runningEnvelope f a floor y ≤ runningEnvelope f a floor x + (Q y - Q x) := by
    apply runningEnvelope_le hc hy
    · linarith [runningEnvelope_floor f a floor x]
    · intro u hu
      by_cases hux : u ≤ x
      · linarith [runningEnvelope_dominates hc hx ⟨hu.1, hux⟩ (floor := floor)]
      · have hu' : u ∈ Icc a b := ⟨hu.1, hu.2.trans hy.2⟩
        have hi := hinc x hx u hu' (le_of_not_ge hux)
        have hQu := hQ hu' hy hu.2
        have hfx := runningEnvelope_dominates hc hx ⟨hx.1, le_rfl⟩ (floor := floor)
        linarith
  linarith

theorem runningEnvelope_lipschitz {f Q : ℝ → ℝ} {a b floor : ℝ} {L : ℝ≥0}
    (hc : ContinuousOn f (Icc a b)) (hQ : MonotoneOn Q (Icc a b))
    (hL : LipschitzOnWith L Q (Icc a b))
    (hinc : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → f y - f x ≤ Q y - Q x) :
    LipschitzOnWith L (runningEnvelope f a floor) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
  have hi := runningEnvelope_increment hc hQ hinc hx hy hxy (floor := floor)
  have hh := hL.dist_le_mul y hy x hx
  rw [dist_comm, Real.dist_eq, abs_of_nonneg hi.1, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hQ hx hy hxy)),
    Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
  linarith

theorem runningEnvelope_cap {f C : ℝ → ℝ} {a b floor : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hC : MonotoneOn C (Icc a b))
    (hfloor : floor ≤ C a) (hcap : ∀ x ∈ Icc a b, f x ≤ C x)
    {x : ℝ} (hx : x ∈ Icc a b) : runningEnvelope f a floor x ≤ C x := by
  apply runningEnvelope_le hc hx (hfloor.trans (hC ⟨le_rfl, hx.1.trans hx.2⟩ hx hx.1))
  intro u hu
  have hu' : u ∈ Icc a b := ⟨hu.1, hu.2.trans hx.2⟩
  exact (hcap u hu').trans (hC hu' hx hu.2)

theorem runningEnvelope_endpoint {f : ℝ → ℝ} {a b floor : ℝ}
    (hab : a ≤ b) (hfloor : floor ≤ f b) (hdom : ∀ u ∈ Icc a b, f u ≤ f b) :
    runningEnvelope f a floor b = f b :=
  ManuscriptCorrections.running_envelope_preserves_endpoint f a b floor hab hfloor hdom

/-- Away from a contact with f, the running maximum is locally constant. -/
theorem runningEnvelope_locally_constant {f : ℝ → ℝ} {a b floor r : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hr : r ∈ Ioo a b)
    (hgap : f r < runningEnvelope f a floor r) :
    runningEnvelope f a floor =ᶠ[nhds r] (fun _ => runningEnvelope f a floor r) := by
  have hfc := hc.continuousAt (Icc_mem_nhds hr.1 hr.2)
  have hnear : ∀ᶠ x in nhds r, f x < runningEnvelope f a floor r :=
    hfc.eventually (gt_mem_nhds hgap)
  obtain ⟨l, u, hrI, hI⟩ := hnear.exists_Ioo_subset
  filter_upwards [Ioo_mem_nhds hrI.1 hrI.2, Icc_mem_nhds hr.1 hr.2] with x hx hxdom
  have hrdom : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
  apply le_antisymm
  · apply runningEnvelope_le hc hxdom (runningEnvelope_floor f a floor r)
    intro v hv
    by_cases hvr : v ≤ r
    · exact runningEnvelope_dominates hc hrdom ⟨hv.1, hvr⟩
    · exact (hI ⟨by linarith [hrI.1], hv.2.trans_lt hx.2⟩).le
  · obtain ⟨v, hv, heq, _⟩ := runningEnvelope_attainment hc hrdom (floor := floor)
    rcases le_total (f v) floor with hvfloor | hvfloor
    · rw [heq, max_eq_left hvfloor]
      exact runningEnvelope_floor f a floor x
    · have hEq : runningEnvelope f a floor r = f v := heq.trans (max_eq_right hvfloor)
      by_cases hvx : v ≤ x
      · rw [hEq]
        exact runningEnvelope_dominates hc hxdom ⟨hv.1, hvx⟩
      · have hvI : v ∈ Ioo l u := ⟨by linarith [hx.1], hv.2.trans_lt hrI.2⟩
        have hh := hI hvI
        rw [hEq] at hh
        change f v < f v at hh
        exact False.elim (lt_irrefl _ hh)

theorem runningEnvelope_hasDerivAt_zero_of_gap {f : ℝ → ℝ} {a b floor r : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hr : r ∈ Ioo a b)
    (hgap : f r < runningEnvelope f a floor r) :
    HasDerivAt (runningEnvelope f a floor) 0 r :=
  (hasDerivAt_const r (runningEnvelope f a floor r)).congr_of_eventuallyEq
    (runningEnvelope_locally_constant hc hr hgap)

theorem runningEnvelope_derivative_at_contact {f : ℝ → ℝ} {a b floor r f' E' : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hr : r ∈ Ioo a b)
    (heq : runningEnvelope f a floor r = f r)
    (hf : HasDerivAt f f' r) (hE : HasDerivAt (runningEnvelope f a floor) E' r) : E' = f' := by
  have hmin : IsLocalMin (fun x => runningEnvelope f a floor x - f x) r := by
    filter_upwards [Icc_mem_nhds hr.1 hr.2] with x hx
    rw [heq, sub_self]
    exact sub_nonneg.mpr (runningEnvelope_dominates hc hx ⟨hx.1, le_rfl⟩)
  have hh := hmin.hasDerivAt_eq_zero (hE.sub hf)
  linarith

/-- At every differentiability point the new score is either zero or exactly
the old score. This is the key selection property in B.1 Step 2. -/
theorem runningEnvelope_derivative_selection {f : ℝ → ℝ} {a b floor r f' E' : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hr : r ∈ Ioo a b)
    (hf : HasDerivAt f f' r) (hE : HasDerivAt (runningEnvelope f a floor) E' r) :
    E' = 0 ∨ E' = f' := by
  have hdom := runningEnvelope_dominates hc ⟨hr.1.le, hr.2.le⟩ ⟨hr.1.le, le_rfl⟩ (floor := floor)
  rcases eq_or_lt_of_le hdom with heq | hgap
  · exact Or.inr (runningEnvelope_derivative_at_contact hc hr heq.symm hf hE)
  · exact Or.inl (hE.unique (runningEnvelope_hasDerivAt_zero_of_gap hc hr hgap))

end OptimalG
