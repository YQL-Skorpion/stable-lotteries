import OptimalG.CompletedPrimitive

/-! Polynomial endpoint completion preserves every shape assumption needed
by the finite-election verifier. -/
namespace OptimalG
open Set MeasureTheory

theorem tailScore_high_fall {z Y H a b : ℝ} (hz : z < 1)
    (h1 : tailOne z Y H ≤ z-1) (h2 : tailTwo z Y H ≤ 0)
    (ha : z ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    tailScore z Y H b-tailScore z Y H a ≤ a-b := by
  have hwa := (tailCoord_mem_Icc z a hz ⟨ha,hab.trans hb⟩).1
  have hwb := (tailCoord_mem_Icc z b hz ⟨ha.trans hab,hb⟩).1
  have hw : tailCoord z a ≤ tailCoord z b :=
    (div_le_div_iff_of_pos_right (sub_pos.mpr hz)).mpr (by linarith)
  have hneg := mul_nonpos_of_nonpos_of_nonneg h2 (add_nonneg hwa hwb)
  have hsum : tailOne z Y H+tailTwo z Y H*(tailCoord z a+tailCoord z b) ≤ z-1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hw)
  have hden : 1-z ≠ 0 := ne_of_gt (sub_pos.mpr hz)
  have he : (1-z)*(tailCoord z b-tailCoord z a)=b-a := by
    unfold tailCoord
    field_simp [hden]
    ring
  unfold tailScore
  nlinarith only [hmul,he]

theorem tailScore_ceiling {lam z Y H : ℝ} (hz : z < 1)
    (h1 : tailOne z Y H ≤ z-1) (h2 : tailTwo z Y H ≤ 0) (hH : H ≤ lam-z) :
    ∀ r ∈ Icc z 1,tailScore z Y H r ≤ lam-r := by
  intro r hr
  have hh := tailScore_high_fall hz h1 h2 (a := z) le_rfl hr.1 hr.2
  rw [tailScore_at_join] at hh
  linarith

/-- The completed curve is an actual `VerifierCurve`, conditional only on
explicit middle-curve shape and endpoint scalar inequalities. -/
theorem completedScore_verifierCurve {lam x J f z Y H : ℝ} {psi : ℝ → ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxl : x ≤ lam) (hlz : lam ≤ z) (hz : z < 1)
    (hpsi : ContinuousOn psi (Icc x z)) (hanti : StrictAntiOn psi (Icc x z))
    (hxjoin : psi x=f) (hzjoin : psi z=H) (hzero : psi lam=0)
    (harea : (∫ r in x..z,psi r)=Y-J)
    (hhead : headSlope x J f < 0) (hhead0 : headInitial x J f ≤ lam)
    (htail1 : tailOne z Y H ≤ z-1) (htail2 : tailTwo z Y H ≤ 0)
    (hceiling : ∀ r ∈ Icc x z,psi r ≤ lam-r)
    (hfall : ∀ a b,lam ≤ a → a ≤ b → b ≤ z → psi b-psi a ≤ a-b) :
    VerifierCurve (completedScore x J f z Y H psi) lam := by
  have hxz := hxl.trans hlz
  have htailNeg : tailOne z Y H < 0 := by linarith
  have hxcap : f ≤ lam-x := by rw [← hxjoin]; exact hceiling x ⟨le_rfl,hxz⟩
  have hzcap : H ≤ lam-z := by rw [← hzjoin]; exact hceiling z ⟨hxz,le_rfl⟩
  have hheadCap := headScore_ceiling x J f lam hx hhead0 hxcap
  have htailCap := tailScore_ceiling hz htail1 htail2 hzcap
  refine ⟨hlam.1,hlam.2,completedScore_continuousOn hx.ne' hxz hpsi hxjoin hzjoin,
    completedScore_strictAntiOn hx hxz hz hhead htailNeg htail2 hanti hxjoin hzjoin,
    completedScore_integral_zero hx hxz hz hpsi hxjoin hzjoin harea,?_,
    completedScore_at_one hx.ne' hxz hz hxjoin hzjoin,?_,?_⟩
  · rw [completedScore_middle hx.ne' hxz hxjoin ⟨hxl,hlz⟩,hzero]
  · intro r hr
    by_cases hrx : r ≤ x
    · rw [completedScore,joinAt_left _ _ hrx]
      exact hheadCap r ⟨hr.1,hrx⟩
    · by_cases hrz : r ≤ z
      · rw [completedScore_middle hx.ne' hxz hxjoin ⟨le_of_not_ge hrx,hrz⟩]
        exact hceiling r ⟨le_of_not_ge hrx,hrz⟩
      · rw [completedScore_tail hx.ne' hxz hxjoin hzjoin (le_of_not_ge hrz)]
        exact htailCap r ⟨le_of_not_ge hrz,hr.2⟩
  · intro a b ha hab hb
    by_cases hbz : b ≤ z
    · rw [completedScore_middle hx.ne' hxz hxjoin ⟨hxl.trans (ha.trans hab),hbz⟩,
        completedScore_middle hx.ne' hxz hxjoin ⟨hxl.trans ha,hab.trans hbz⟩]
      exact hfall a b ha hab hbz
    · by_cases haz : a ≤ z
      · rw [completedScore_tail hx.ne' hxz hxjoin hzjoin (le_of_not_ge hbz),
          completedScore_middle hx.ne' hxz hxjoin ⟨hxl.trans ha,haz⟩]
        have hleft := hfall a z ha haz le_rfl
        rw [hzjoin] at hleft
        have hright := tailScore_high_fall hz htail1 htail2 (a := z) le_rfl (le_of_not_ge hbz) hb
        rw [tailScore_at_join] at hright
        linarith
      · rw [completedScore_tail hx.ne' hxz hxjoin hzjoin (le_of_not_ge hbz),
          completedScore_tail hx.ne' hxz hxjoin hzjoin (le_of_not_ge haz)]
        exact tailScore_high_fall hz htail1 htail2 (le_of_not_ge haz) hab hb

end OptimalG
