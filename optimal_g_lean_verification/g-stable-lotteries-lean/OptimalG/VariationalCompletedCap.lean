import OptimalG.VariationalCompletedCurve
import OptimalG.VariationalHeadSlopeBand
import OptimalG.VerifierPrimitiveCap

/-! The completed primitive satisfies the binary cap on the entire interval
[0,.53]. The affine head is compared by finite slopes, the recovered middle
uses admissibility, and the straight/high part uses the score ceiling. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem Admissible.capScore_ge_line_after_xHi {lam r : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hr : r∈Icc xHi (0.53:ℝ)) :
    lam-r≤capScore lam d.S r := by
  have hL := hd.compact_lambdaRange
  have hnum := mul_le_mul hL.2 hd.slack_upper
    (by linarith [hd.slack_lower] : 0≤d.S) (by norm_num : (0:ℝ)≤0.562330)
  have hden : (0.47:ℝ)^2≤(1-r)^2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith only [hr.2]) 2
  have hfrac : lam*d.S/(1-r)^2≤(0.068:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (by linarith only [hr.2] : 0<1-r))).mpr
    nlinarith only [hnum,hden]
  have hr0 : (0.38:ℝ)≤r := by convert! hr.1 using 1 <;> norm_num [xHi]
  unfold capScore
  linarith only [hfrac,hr0,hL.2]

theorem Admissible.cap_ge_quadratic_after_xHi {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    ∀ r∈Icc xHi (0.53:ℝ),quadratic lam r-d.S≤cap lam d.S r := by
  have hL := hd.compact_lambdaRange
  have hL0 : 0≤lam := by linarith only [hL.1]
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤0.562325) hL.1 2
  have hprod := mul_le_mul hd.slack_lower
    (show (0.05767:ℝ)≤0.62-lam by linarith only [hL.2])
    (by norm_num : (0:ℝ)≤0.05767) (by linarith [hd.slack_lower] : 0≤d.S)
  have hstart : 0≤cap lam d.S xHi-quadratic lam xHi+d.S := by
    unfold cap quadratic
    norm_num [xHi]
    nlinarith only [hprod,hsq,hL.2]
  have hder (r : ℝ) (hr : r∈Icc xHi (0.53:ℝ)) :
      HasDerivAt (fun r=>cap lam d.S r-quadratic lam r)
        (capScore lam d.S r-(lam-r)) r :=
    (cap_hasDerivAt lam d.S r (ne_of_lt (by linarith only [hr.2]))).sub
      (quadratic_hasDerivAt lam r)
  intro r hr
  have hh := reference_primitive_lower_increment hder
    (fun t ht => sub_nonneg.mpr (hd.capScore_ge_line_after_xHi ⟨ht.1.le,ht.2.le⟩))
    xHi ⟨le_rfl,by norm_num [xHi]⟩ r hr hr.1
  linarith only [hh,hstart]

theorem head_primitive_le_cap {lam : ℝ} {d : LowRankData} {phi : ℝ → ℝ}
    (hd : Admissible lam d) (h : VerifierCurve phi lam)
    (hhead : ∀ r∈Icc (0:ℝ) 0.2635,
      phi r=phi 0+headSlope 0.2635 (cap lam d.S 0.2635) (capScore lam d.S 0.2635)*r)
    (hscore : phi 0.2635=capScore lam d.S 0.2635)
    (hanchor : curvePrimitive phi 0.2635=cap lam d.S 0.2635) :
    ∀ r∈Icc (0:ℝ) 0.2635,curvePrimitive phi r≤cap lam d.S r := by
  have hbelow : ∀ u∈Icc (0:ℝ) 0.2635,capScore lam d.S u≤phi u := by
    intro u hu
    have hh := hd.cap_increment_ge_headSlope hu.2 (by norm_num [xHi])
    have he := hhead 0.2635 ⟨by norm_num,le_rfl⟩
    rw [hscore] at he
    rw [hhead u hu]
    nlinarith only [hh,he]
  intro r hr
  have hcapCont : ContinuousOn (capScore lam d.S) (uIcc r (0.2635:ℝ)) := by
    intro u hu
    rw [uIcc_of_le hr.2] at hu
    exact (capScore_hasDerivAt lam d.S u (ne_of_lt (by linarith only [hu.2]))).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hr.2 hcapCont.intervalIntegrable
    (h.continuous.mono (uIcc_subset_Icc ⟨hr.1,by linarith only [hr.2]⟩
      ⟨by norm_num,by norm_num⟩)).intervalIntegrable
    (fun u hu => hbelow u ⟨hr.1.trans hu.1,hu.2⟩)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => cap_hasDerivAt lam d.S u (ne_of_lt (by
        rw [uIcc_of_le hr.2] at hu;linarith only [hu.2]))) hcapCont.intervalIntegrable,
    ←h.primitive_difference hr.1 hr.2 (by norm_num),hanchor] at hi
  linarith only [hi]

theorem completedVariationalScore_primitive_le_cap {lam c b : ℝ} {d : LowRankData}
    {psi Y : ℝ → ℝ} (hd : Admissible lam d) (hc : (0.2635:ℝ)≤c) (hb : zStart≤b)
    (hcurve : VerifierCurve (completedVariationalScore 0.2635 lam d (capRegularScore lam d.S c psi) Y b) lam)
    (hprim : ∀ r∈Icc (0.2635:ℝ) xHi,
      curvePrimitive (completedVariationalScore 0.2635 lam d (capRegularScore lam d.S c psi) Y b) r=
      primitive lam d r)
    (hanchor : primitive lam d xHi=quadratic lam xHi-d.S) :
    ∀ r∈Icc (0:ℝ) 0.53,
      curvePrimitive (completedVariationalScore 0.2635 lam d (capRegularScore lam d.S c psi) Y b) r≤cap lam d.S r := by
  let phi := completedVariationalScore 0.2635 lam d (capRegularScore lam d.S c psi) Y b
  have hscore : phi 0.2635=capScore lam d.S 0.2635 := by
    dsimp only [phi]
    rw [completedVariationalScore_low (a:=0.2635) (by norm_num) (by norm_num [xHi]) hb
      ⟨le_rfl,by norm_num [xHi]⟩,capRegularScore_left _ _ _ _ hc]
  have hhead : ∀ r∈Icc (0:ℝ) 0.2635,
      phi r=phi 0+headSlope 0.2635 (cap lam d.S 0.2635) (capScore lam d.S 0.2635)*r := by
    intro r hr
    simp only [phi,completedVariationalScore,completedScore,joinAt_left _ _ hr.2,
      joinAt_left _ _ (by norm_num : (0:ℝ)≤0.2635),capRegularScore_left _ _ _ _ hc,
      headScore,mul_zero,add_zero]
  have ha : curvePrimitive phi 0.2635=cap lam d.S 0.2635 := by
    rw [hprim 0.2635 ⟨le_rfl,by norm_num [xHi]⟩]
    simp only [primitive,if_pos (by norm_num [ell] : (0.2635:ℝ)≤ell)]
  have hx : curvePrimitive phi xHi=quadratic lam xHi-d.S := by
    rw [hprim xHi ⟨by norm_num [xHi],le_rfl⟩,hanchor]
  intro r hr
  by_cases hra : r≤(0.2635:ℝ)
  · exact head_primitive_le_cap hd hcurve hhead hscore ha r ⟨hr.1,hra⟩
  · by_cases hrx : r≤xHi
    · rw [hprim r ⟨le_of_not_ge hra,hrx⟩]
      unfold primitive
      split_ifs with hre hrt
      · exact le_rfl
      · exact hd.lowPrimitive_le_cap ⟨le_of_not_ge hre,hrx.trans (by norm_num [xHi,tEnd])⟩
      · exact False.elim (hrt (hrx.trans (by norm_num [xHi,tEnd])))
    · exact (hcurve.primitive_le_quadratic_after_anchor
        (by constructor <;> norm_num [xHi]) hx r ⟨le_of_not_ge hrx,by linarith only [hr.2]⟩).trans
        (hd.cap_ge_quadratic_after_xHi r ⟨le_of_not_ge hrx,hr.2⟩)

end OptimalG.Variational
