import OptimalG.FixedControlDeficit

/-! A second integration of the fixed-control inequality gives a cubic
score-deficit lower bound. Its coefficients are rational functions of the
fixed control; no exponential interval calculation is needed. -/
namespace OptimalG
open Set

theorem positive_part_deficit_growth_cubic {D E : ℝ→ℝ} {a b c m alpha : ℝ}
    (hc : c∈Icc a b) (hm : 0<m) (halpha : 0≤alpha)
    (hcont : ContinuousOn D (Icc a b))
    (hd : ∀ r∈Ioo a b,HasDerivAt D (E r) r)
    (hD : ∀ r∈Icc a b,0≤D r) (hE : ∀ r∈Icc a b,0≤E r)
    (hfield : ∀ r∈Icc a b,m*(r-c)+alpha*D r≤E r) :
    (∀ r∈Icc c b,(m/2)*(r-c)^2+(alpha*m/6)*(r-c)^3≤D r) ∧
    ∀ r∈Icc a b,
      max (m*(r-c)) 0+alpha/(2*m)*(max (m*(r-c)) 0)^2+
        alpha^2/(6*m^2)*(max (m*(r-c)) 0)^3≤E r := by
  have hbase := positive_part_deficit_growth hc hm halpha hcont hd hD hE hfield
  let F : ℝ→ℝ := fun r=>D r-(m/2)*(r-c)^2-(alpha*m/6)*(r-c)^3
  have hsub : Icc c b⊆Icc a b := Icc_subset_Icc hc.1 le_rfl
  have hFc : ContinuousOn F (Icc c b) := by
    have hDc := hcont.mono hsub
    dsimp [F]
    fun_prop
  have hFd (r : ℝ) (hr : r∈interior (Icc c b)) :
      HasDerivAt F (E r-m*(r-c)-(alpha*m/2)*(r-c)^2) r := by
    rw [interior_Icc] at hr
    convert! ((hd r ⟨hc.1.trans_lt hr.1,hr.2⟩).sub
      ((((hasDerivAt_id r).sub_const c).pow 2).const_mul (m/2))).sub
      ((((hasDerivAt_id r).sub_const c).pow 3).const_mul (alpha*m/6)) using 1 <;>
      first | rfl | (dsimp [F]; ring)
  have hmono : MonotoneOn F (Icc c b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hFc
    · intro r hr
      exact (hFd r hr).hasDerivWithinAt
    · intro r hr
      have hrc := (interior_subset hr).1
      have hh := hbase r (hsub (interior_subset hr))
      rw [max_eq_left (mul_nonneg hm.le (sub_nonneg.mpr hrc))] at hh
      have hid : alpha/(2*m)*(m*(r-c))^2=(alpha*m/2)*(r-c)^2 := by
        field_simp [hm.ne'] <;> ring
      rw [hid] at hh
      linarith only [hh]
  have hprim (r : ℝ) (hr : r∈Icc c b) :
      (m/2)*(r-c)^2+(alpha*m/6)*(r-c)^3≤D r := by
    have hh := hmono ⟨le_rfl,hc.2⟩ hr hr.1
    have hz := hD c hc
    dsimp [F] at hh
    nlinarith only [hh,hz]
  refine ⟨hprim,?_⟩
  intro r hr
  by_cases hrc : r≤c
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hm.le (sub_nonpos.mpr hrc))]
    simpa using hE r hr
  · have hcr := (lt_of_not_ge hrc).le
    have hp := hprim r ⟨hcr,hr.2⟩
    have hh := hfield r hr
    have hs := mul_le_mul_of_nonneg_left hp halpha
    have hid : alpha/(2*m)*(m*(r-c))^2+
        alpha^2/(6*m^2)*(m*(r-c))^3=
        alpha*((m/2)*(r-c)^2+(alpha*m/6)*(r-c)^3) := by
      field_simp [hm.ne'] <;> ring
    rw [max_eq_left (mul_nonneg hm.le (sub_nonneg.mpr hcr)),add_assoc,hid]
    linarith only [hh,hs]

end OptimalG
