import OptimalG.HighMassGeometry

/-! C.5 assembly from curve shape and explicit bounded numerical tests.
`HighMassIntervalBounds` records the remaining D.3 certificate facts. Its fields
are not asserted here: the theorem below discharges the infinite analytic
reductions, including all masses above 0.925 and all high splits. -/
namespace OptimalG
open Set

/-- The finite-domain quantities left to the interval certificates of D.3. -/
structure HighMassIntervalBounds (phi : ℝ → ℝ) (lam xh : ℝ) : Prop where
  intermediate_beta : ∀ p ∈ Ioc lam (13/20:ℝ),
    p/curvePrimitive phi p ≤ 2483/500
  intermediate_margin : ∀ p ∈ Ioc lam (13/20:ℝ),
    curvePrimitive phi p ≤ p*(phi 0-lam+1-p)
  intermediate_eta_zero : ∀ p ∈ Ioc lam (13/20:ℝ),
    intermediateEta phi lam xh p * phi 0 ≤ lam+intermediateCorrection phi lam p
  intermediate_mixed_lower : ∀ p ∈ Ioc lam (13/20:ℝ), ∀ q ∈ Icc (0:ℝ) lam,
    ∀ z ∈ Icc (31/40:ℝ) (7/8:ℝ),
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam xh p*phi z ≤ 0
  intermediate_mixed_upper : ∀ p ∈ Ioc lam (13/20:ℝ), ∀ q ∈ Icc (0:ℝ) lam,
    ∀ z ∈ Icc (7/8:ℝ) 1,
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
      intermediateEta phi lam xh p*phi z ≤ 0
  low_ratio : ∀ x ∈ Ico (0:ℝ) lam, lowRankRatio phi lam x ≤ 129/100
  large_scale : ∀ p ∈ Icc (13/20:ℝ) (22/25:ℝ),
    129/100 ≤ (p/curvePrimitive phi p)*(1-p)
  far_clipped : ∀ p ∈ Ico (22/25:ℝ) 1, ∀ x ∈ Icc (9/50:ℝ) (9/25:ℝ),
    ∀ q ∈ Icc (0:ℝ) (9/50:ℝ), 9/50 ≤ x-q →
    q-x+(p/curvePrimitive phi p)*(1-p)*(packingDelta phi p q/(1-p)-phi x) ≤ 0
  large_mixed_lower : ∀ p ∈ Icc (13/20:ℝ) (37/40:ℝ), ∀ q ∈ Icc (0:ℝ) lam,
    ∀ z ∈ Icc p (7/8:ℝ),
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z ≤ 0
  large_mixed_upper : ∀ p ∈ Icc (13/20:ℝ) (37/40:ℝ), ∀ q ∈ Icc (0:ℝ) lam,
    ∀ z ∈ Icc (7/8:ℝ) 1, p ≤ z →
    z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+phi z ≤ 0

/-- C.24 and C.25 use the same normalized coefficient and meet at mass 0.65. -/
noncomputable def highMassCorrection (phi : ℝ → ℝ) (lam p x : ℝ) : ℝ :=
  if p ≤ 13/20 then intermediateCorrection phi lam p
  else largeMassCorrection phi lam p (p/curvePrimitive phi p) x

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- Intermediate masses: the interval mixed tests begin at 0.775. The entire
straight middle segment, both ratio conditions and both low tests are derived. -/
theorem highMass_intermediate {xh slope p : ℝ}
    (hlam : lam ∈ Ioo (9/25:ℝ) (13/20:ℝ)) (hxh : xh ∈ Ioo (0:ℝ) lam)
    (haff : ∀ x ∈ Icc (0:ℝ) xh, phi x=phi 0+slope*x)
    (hline : ∀ x ∈ Icc (9/25:ℝ) (31/40:ℝ), phi x=lam-x)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 31/40 → a-b ≤ phi b-phi a)
    (hb : ∀ q ∈ Icc (0:ℝ) lam, q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam)
    (hn : HighMassIntervalBounds phi lam xh) (hp : p ∈ Ioc lam (13/20:ℝ)) :
    HighMassTest phi lam p (p/curvePrimitive phi p)
      (fun _ => intermediateCorrection phi lam p) := by
  have hp' : p ∈ Ioo lam 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨h.lam_pos.trans hp.1,hp'.2⟩
  have hbeta : 0 ≤ p/curvePrimitive phi p := (div_pos hp0.1 (h.primitive_pos hp0)).le
  have hnorm : (p/curvePrimitive phi p)*curvePrimitive phi p=p :=
    div_mul_cancel₀ p (h.primitive_pos hp0).ne'
  have hc : (p/curvePrimitive phi p)*curvePrimitive phi (1-p) ≤ lam := by
    have hh := hb 0 ⟨le_rfl,h.lam_pos.le⟩
    simpa [packingDelta,curvePrimitive] using hh
  have hc0 : 0 ≤ intermediateCorrection phi lam p := sub_nonneg.mpr hc
  have hlow (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbl : b ≤ lam) :
      phi a-phi b ≤ b-a := by
    have hh := hfall a b ha hab (by linarith [hlam.2])
    linarith
  have hline' : ∀ x ∈ Icc lam (31/40:ℝ), phi x=lam-x := by
    intro x hx
    exact hline x ⟨hlam.1.le.trans hx.1,hx.2⟩
  apply h.highMassTest_constantCorrection (eta := intermediateEta phi lam xh p)
    hp' hbeta hnorm hc
  · intro q hq
    exact h.normalized_binary_le_zero_split hp0
      (fun u hu => by have hh := hlow 0 u le_rfl hu.1 hu.2; linarith)
      (h.normalized_binary_gap_of_primitive hp0 (hn.intermediate_margin p hp))
      hq.1 (hq.2.trans hp.1.le) hq.2
  · apply h.constantCorrection_ratio hlow hp' ⟨by norm_num,hlam.1.le⟩ hbeta
    · have hh := hn.intermediate_beta p hp
      nlinarith
    · exact hc
    · intro x hx
      exact hline x ⟨hx.1,by linarith [hx.2,hlam.2]⟩
  · exact h.constantCorrection_eta_bound hxh hc0 haff (hn.intermediate_eta_zero p hp)
  · intro q hq z hz
    have he : 0 ≤ intermediateEta phi lam xh p := by
      unfold intermediateEta
      exact add_nonneg zero_le_one (div_nonneg hc0 (h.positive ⟨hxh.1.le,hxh.2⟩).le)
    have hhigh (z : ℝ) (hz : z ∈ Icc (31/40:ℝ) 1) :
        z+q-lam+(p/curvePrimitive phi p)*packingK phi p q z+
          intermediateEta phi lam xh p*phi z ≤ 0 := by
      by_cases hzcut : z ≤ 7/8
      · exact hn.intermediate_mixed_lower p hp q hq z ⟨hz.1,hzcut⟩
      · exact hn.intermediate_mixed_upper p hp q hq z ⟨le_of_not_ge hzcut,hz.2⟩
    by_cases hzm : z ≤ 31/40
    · exact h.highMass_middle_of_endpoint hp.1.le hq (by linarith [hp.2])
        (by norm_num) hbeta he hnorm hline' hfall
        (hhigh (31/40) ⟨le_rfl,by norm_num⟩) z ⟨hz.1,hzm⟩
    · exact hhigh z ⟨le_of_not_ge hzm,hz.2⟩

/-- The low clipped correction is automatic on the entire mass interval after
combining the zero-correction, short-split and bounded far-split cases. -/
theorem highMass_clipped_low {xh p : ℝ}
    (hlam : lam ∈ Ioo (9/25:ℝ) (13/20:ℝ))
    (hline : ∀ x ∈ Icc (9/25:ℝ) (31/40:ℝ), phi x=lam-x)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 31/40 → a-b ≤ phi b-phi a)
    (hcone : ∀ u ∈ Icc (22/25:ℝ) 1,
      -1+2*(1-u) ≤ phi u ∧ phi u ≤ -1+(67/10)*(1-u))
    (hb : ∀ q ∈ Icc (0:ℝ) lam, q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam)
    (hn : HighMassIntervalBounds phi lam xh) (hp : p ∈ Ico (13/20:ℝ) 1) :
    ∀ x ∈ Ico (0:ℝ) lam, ∀ q, 0 ≤ q → q ≤ x →
      q+(p/curvePrimitive phi p)*packingDelta phi p q+
        largeMassCorrection phi lam p (p/curvePrimitive phi p) x ≤ lam := by
  have hpl : lam < p := hlam.2.trans_le hp.1
  have hp0 : 0 < p := h.lam_pos.trans hpl
  have hbeta : 0 ≤ p/curvePrimitive phi p := (div_pos hp0 (h.primitive_pos ⟨hp0,hp.2⟩)).le
  have hlow (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbl : b ≤ lam) :
      phi a-phi b ≤ b-a := by
    have hh := hfall a b ha hab (by linarith [hlam.2])
    linarith
  intro x hx q hq hqx
  have hbinary := hb q ⟨hq,hqx.trans hx.2.le⟩
  by_cases hp88 : p ≤ 22/25
  · rw [h.largeMassCorrection_eq_zero_of_ratio hx
      ((hn.low_ratio x hx).trans (hn.large_scale p ⟨hp.1,hp88⟩)),add_zero]
    exact hbinary
  · have hp88' : p ∈ Ico (22/25:ℝ) 1 := ⟨le_of_not_ge hp88,hp.2⟩
    have ht := h.highMass_tail_coefficient hp88'
      (fun u hu => hcone u ⟨hp88'.1.trans hu.1,hu.2⟩)
    have hshort := clipped_short_conditions
      (show 1-p ∈ Icc (0:ℝ) (3/25:ℝ) by constructor <;> linarith [hp.2,hp88'.1])
      (mul_nonneg hbeta (sub_pos.mpr hp.2).le)
      (by simpa only [sub_sub_cancel] using ht.2)
    by_cases hc : 0 < largeMassCorrection phi lam p (p/curvePrimitive phi p) x
    · by_cases hv : x-q ≤ 9/50
      · exact h.lowFirst_largeCorrection_short hlow ⟨hpl,hp.2⟩ hx hq hqx hbeta
          hshort.1 (hshort.2 (x-q) ⟨sub_nonneg.mpr hqx,hv⟩) hbinary
      · have hxc := h.largeMassCorrection_pos_before_line hx
          (fun y hy => hline y ⟨hy.1,by linarith [hy.2,hlam.2]⟩) ht.1 hc
        apply h.lowFirst_largeCorrection_far hp.2 hc
        exact hn.far_clipped p hp88' x ⟨by linarith,hxc.le⟩ q
          ⟨hq,by linarith⟩ (le_of_not_ge hv)
    · have heq : largeMassCorrection phi lam p (p/curvePrimitive phi p) x=0 :=
        le_antisymm (le_of_not_gt hc) (le_max_right _ _)
      rw [heq,add_zero]
      exact hbinary

/-- All mixed large-mass tests above 0.925 are analytic consequences of the
two-class test. The finite mixed certificates stop at 0.925. -/
theorem highMass_large {xh p : ℝ}
    (hlam : lam ∈ Ioo (9/25:ℝ) (13/20:ℝ))
    (hline : ∀ x ∈ Icc (9/25:ℝ) (31/40:ℝ), phi x=lam-x)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 31/40 → a-b ≤ phi b-phi a)
    (hcone : ∀ u ∈ Icc (22/25:ℝ) 1,
      -1+2*(1-u) ≤ phi u ∧ phi u ≤ -1+(67/10)*(1-u))
    (hb : ∀ q ∈ Icc (0:ℝ) lam, q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam)
    (hn : HighMassIntervalBounds phi lam xh) (hp : p ∈ Ico (13/20:ℝ) 1) :
    HighMassTest phi lam p (p/curvePrimitive phi p)
      (largeMassCorrection phi lam p (p/curvePrimitive phi p)) := by
  have hpl : lam < p := hlam.2.trans_le hp.1
  apply highMassTest_largeCorrection h ⟨hpl,hp.2⟩
    (h.highMass_clipped_low hlam hline hfall hcone hb hn hp) hb
  intro q hq z hz
  by_cases hp925 : p ≤ 37/40
  · by_cases hz875 : z ≤ 7/8
    · exact hn.large_mixed_lower p ⟨hp.1,hp925⟩ q hq z ⟨hz.1,hz875⟩
    · exact hn.large_mixed_upper p ⟨hp.1,hp925⟩ q hq z ⟨le_of_not_ge hz875,hz.2⟩ hz.1
  · apply mixedTest_near_one h ⟨le_of_not_ge hp925,hp.2⟩ hpl _ _ hb q hq z hz
    · have hh := hline (lam+(1-p)) ⟨by linarith [hlam.1,hp.2],by linarith [hlam.2]⟩
      linarith
    · intro u hu
      have hh := (hcone u ⟨by linarith [hu.1],hu.2⟩).2
      nlinarith [hu.2]

/-- The entire C.5 mass range, with the actual piecewise correction. The
remaining assumptions are curve shape, the C.3 binary result, and the listed
bounded D.3 interval facts. -/
theorem highMass_verifier {xh slope : ℝ}
    (hlam : lam ∈ Ioo (9/25:ℝ) (13/20:ℝ)) (hxh : xh ∈ Ioo (0:ℝ) lam)
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (haff : ∀ x ∈ Icc (0:ℝ) xh, phi x=phi 0+slope*x)
    (hline : ∀ x ∈ Icc (9/25:ℝ) (31/40:ℝ), phi x=lam-x)
    (hfall : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 31/40 → a-b ≤ phi b-phi a)
    (hcone : ∀ u ∈ Icc (22/25:ℝ) 1,
      -1+2*(1-u) ≤ phi u ∧ phi u ≤ -1+(67/10)*(1-u))
    (hbinary : ∀ p ∈ Ioo lam 1, ∀ q ∈ Icc (0:ℝ) lam,
      q+(p/curvePrimitive phi p)*packingDelta phi p q ≤ lam)
    (hn : HighMassIntervalBounds phi lam xh) :
    VerifierOn (Ioo lam 1) phi lam (fun p => p/curvePrimitive phi p)
      (highMassCorrection phi lam) := by
  have ht (p : ℝ) (hp : p ∈ Ioo lam 1) :
      HighMassTest phi lam p (p/curvePrimitive phi p) (highMassCorrection phi lam p) := by
    by_cases hpm : p ≤ 13/20
    · have heq : highMassCorrection phi lam p = fun _ => intermediateCorrection phi lam p := by
        funext x; exact if_pos hpm
      rw [heq]
      exact h.highMass_intermediate hlam hxh haff hline hfall (hbinary p hp) hn ⟨hp.1,hpm⟩
    · have heq : highMassCorrection phi lam p = largeMassCorrection phi lam p (p/curvePrimitive phi p) := by
        funext x; exact if_neg hpm
      rw [heq]
      exact h.highMass_large hlam hline hfall hcone (hbinary p hp) hn ⟨le_of_not_ge hpm,hp.2⟩
  have hv (p : ℝ) (hp : p ∈ Ioo lam 1) := highMassTest_verifier h hc hp (ht p hp)
  constructor
  · intro p hp; exact (hv p hp).beta_nonneg p rfl
  · intro p hp; exact (hv p hp).corr_nonneg p rfl
  · intro p hp; exact (hv p hp).low_first p rfl
  · intro p hp; exact (hv p hp).low_second p rfl
  · intro p hp; exact (hv p hp).high_first p rfl
  · intro p hp; exact (hv p hp).high_second p rfl

end VerifierCurve
end OptimalG
