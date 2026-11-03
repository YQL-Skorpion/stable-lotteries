import OptimalG.FixedControlCubicDeficit

namespace OptimalG

noncomputable def cubicControlDeficit (m alpha c z : ℝ) : ℝ :=
  m*(z-c)+(alpha*m/2)*(z-c)^2+(alpha^2*m/6)*(z-c)^3

/-- The unclipped cubic remains a valid lower bound before the crossing,
where it is nonpositive. This removes a numerical case split. -/
theorem cubicControlDeficit_le_clipped {m : ℝ} (hm : 0<m) (alpha c z : ℝ) :
    cubicControlDeficit m alpha c z≤
      max (m*(z-c)) 0+alpha/(2*m)*(max (m*(z-c)) 0)^2+
        alpha^2/(6*m^2)*(max (m*(z-c)) 0)^3 := by
  by_cases hz : c≤z
  · rw [max_eq_left (mul_nonneg hm.le (sub_nonneg.mpr hz))]
    apply le_of_eq
    unfold cubicControlDeficit
    field_simp [hm.ne'] <;> ring
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hm.le (by linarith only [hz]))]
    simp only [zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero,add_zero]
    have hf : 0≤1+alpha*(z-c)/2+alpha^2*(z-c)^2/6 := by
      nlinarith only [sq_nonneg (2*alpha*(z-c)+3)]
    have hh := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hm.le (show z-c≤0 by linarith only [hz])) hf
    unfold cubicControlDeficit
    nlinarith only [hh]

/-- The cubic is increasing on the entire real line, including before its
zero, because the averaged derivative is a sum of squares. -/
theorem cubicControlDeficit_monotone {m : ℝ} (hm : 0≤m) (alpha c : ℝ) :
    Monotone (cubicControlDeficit m alpha c) := by
  intro a b hab
  let B := 1+alpha*((a-c)+(b-c))/2+
    alpha^2*((a-c)^2+(a-c)*(b-c)+(b-c)^2)/6
  have hB : 0≤B := by
    dsimp [B]
    nlinarith only [sq_nonneg (alpha*(a-c)+alpha*(b-c)+2),
      sq_nonneg (alpha*(a-c)-alpha*(b-c))]
  have hmul := mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hab)) hB
  have hid : cubicControlDeficit m alpha c b-cubicControlDeficit m alpha c a=
      m*(b-a)*B := by
    dsimp [cubicControlDeficit,B]
    ring
  exact sub_nonneg.mp (hid.symm ▸ hmul)

end OptimalG
