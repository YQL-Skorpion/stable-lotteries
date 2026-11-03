import OptimalG.SupportingCoefficients

/-! The open-rank supporting infimum used for the small-mass coefficients in
Appendix C.4. Attainment follows from the compact support maximum, including
its zero-score endpoint, and does not require a differentiable minimizing rank. -/
namespace OptimalG
open Set

noncomputable def supportMinimum (phi : ℝ → ℝ) (lam m : ℝ) : ℝ :=
  sInf ((fun x => (m-x)/phi x) '' Ico 0 lam)

private theorem exists_supporting_minimum {phi : ℝ → ℝ} {lam m : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x) (hm : lam<m) :
    ∃ eta : ℝ, 0<eta ∧ ∃ x ∈ Ico 0 lam, eta=(m-x)/phi x ∧
      ∀ y ∈ Ico 0 lam, eta≤(m-y)/phi y := by
  let K : Set ℝ := Icc 0 lam
  have hK : IsCompact K := isCompact_Icc
  have hne : K.Nonempty := ⟨0,⟨le_rfl,hlam.le⟩⟩
  have hzero : supportMaximum phi K 0=lam := by
    obtain ⟨x,hx,he,hmax⟩ := supportMaximum_attained phi K hK hne hc 0
    have hh := hmax lam ⟨hlam.le,le_rfl⟩
    simp only [zero_mul,add_zero] at he hh
    exact he.trans (le_antisymm hx.2 hh)
  have hp0 : 0<phi 0 := hp 0 ⟨le_rfl,hlam⟩
  let B := (m+1)/phi 0
  have hB : 0<B := div_pos (by linarith) hp0
  have hBmul : B*phi 0=m+1 := div_mul_cancel₀ _ (ne_of_gt hp0)
  have hF : m≤supportMaximum phi K B := by
    have hh := le_supportMaximum phi K hK hne hc B 0 ⟨le_rfl,hlam.le⟩
    simp only [zero_add,hBmul] at hh
    linarith
  obtain ⟨eta,heta,heq⟩ := intermediate_value_Icc hB.le
    (supportMaximum_continuous phi K hK hc).continuousOn
    (show m ∈ Icc (supportMaximum phi K 0) (supportMaximum phi K B) by
      rw [hzero]; exact ⟨hm.le,hF⟩)
  have heta0 : 0<eta := by
    rcases eq_or_lt_of_le heta.1 with he | he
    · rw [← he,hzero] at heq
      exact False.elim (ne_of_lt hm heq)
    · exact he
  obtain ⟨x,hx,hmaxeq,hmax⟩ := supportMaximum_attained phi K hK hne hc eta
  have hxlt : x<lam := by
    rcases lt_or_eq_of_le hx.2 with he | he
    · exact he
    · rw [he,hz,mul_zero,add_zero,heq] at hmaxeq
      exact False.elim (ne_of_gt hm hmaxeq)
  have hxI : x ∈ Ico 0 lam := ⟨hx.1,hxlt⟩
  have hxpos := hp x hxI
  refine ⟨eta,heta0,x,hxI,?_,?_⟩
  · apply (eq_div_iff (ne_of_gt hxpos)).mpr
    rw [heq] at hmaxeq
    linarith
  · intro y hy
    apply (le_div_iff₀ (hp y hy)).mpr
    have hh := hmax y ⟨hy.1,hy.2.le⟩
    rw [← hmaxeq,heq] at hh
    linarith

/-- The infimum over ranks strictly below the zero-score rank is attained.
The strict margin m>λ excludes the zero-score endpoint from a compact maximizer. -/
theorem supportMinimum_attained {phi : ℝ → ℝ} {lam m : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x) (hm : lam<m) :
    0<supportMinimum phi lam m ∧ ∃ x ∈ Ico 0 lam,
      supportMinimum phi lam m=(m-x)/phi x ∧
      ∀ y ∈ Ico 0 lam, supportMinimum phi lam m≤(m-y)/phi y := by
  obtain ⟨eta,heta,x,hx,he,hmin⟩ := exists_supporting_minimum hlam hc hz hp hm
  have hleast : IsLeast ((fun x => (m-x)/phi x) '' Ico 0 lam) eta := by
    refine ⟨⟨x,hx,he.symm⟩,?_⟩
    rintro v ⟨y,hy,rfl⟩
    exact hmin y hy
  have hval : supportMinimum phi lam m=eta := hleast.csInf_eq
  rw [hval]
  exact ⟨heta,x,hx,he,hmin⟩

theorem supportMinimum_le_ratio {phi : ℝ → ℝ} {lam m x : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hm : lam<m) (hx : x ∈ Ico 0 lam) :
    supportMinimum phi lam m≤(m-x)/phi x := by
  obtain ⟨_,y,hy,he,hmin⟩ := supportMinimum_attained hlam hc hz hp hm
  exact hmin x hx

/-- Evaluation at an old minimizing rank gives an exact finite comparison. -/
theorem supportMinimum_compare_at_minimizer {phi : ℝ → ℝ} {lam m₁ m₂ x : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hm₂ : lam<m₂) (hx : x ∈ Ico 0 lam)
    (hmin : supportMinimum phi lam m₁=(m₁-x)/phi x) :
    supportMinimum phi lam m₂-supportMinimum phi lam m₁≤(m₂-m₁)/phi x := by
  have hh := supportMinimum_le_ratio hlam hc hz hp hm₂ hx
  rw [hmin]
  calc
    supportMinimum phi lam m₂-(m₁-x)/phi x ≤ (m₂-x)/phi x-(m₁-x)/phi x := sub_le_sub_right hh _
    _=(m₂-m₁)/phi x := by rw [← sub_div]; congr 1; ring

/-- The score ceiling at an old minimizer provides the one-sided rate needed
for leftward transport. The ceiling is an explicit later numerical input. -/
theorem supportMinimum_decrease_bound {phi : ℝ → ℝ} {lam m₁ m₂ x A : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hm₂ : lam<m₂) (hmm : m₂≤m₁) (hx : x ∈ Ico 0 lam)
    (hmin : supportMinimum phi lam m₁=(m₁-x)/phi x) (hA : phi x≤A) :
    supportMinimum phi lam m₂-supportMinimum phi lam m₁≤(m₂-m₁)/A := by
  apply (supportMinimum_compare_at_minimizer hlam hc hz hp hm₂ hx hmin).trans
  have hxpos := hp x hx
  have hApos := hxpos.trans_le hA
  apply (div_le_div_iff₀ hxpos hApos).mpr
  nlinarith

/-- Consequently the supporting infimum is strictly increasing in its target. -/
theorem supportMinimum_strictMonoOn {phi : ℝ → ℝ} {lam : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x) :
    StrictMonoOn (supportMinimum phi lam) (Ioi lam) := by
  intro m₁ hm₁ m₂ hm₂ hlt
  obtain ⟨_,x,hx,hmin,_⟩ := supportMinimum_attained hlam hc hz hp hm₂
  have hh := supportMinimum_compare_at_minimizer hlam hc hz hp hm₁ hx hmin
  have hn : (m₁-m₂)/phi x<0 := div_neg_of_neg_of_pos (sub_neg.mpr hlt) (hp x hx)
  linarith

end OptimalG
