import OptimalG.VariationalHighShape

/-! A finite lower bound for the control field on a quadratic comparison
curve yields the genuine early-continuation deficit used in C.3. -/
namespace OptimalG.Variational
open Set MeasureTheory

/-- This scalar residual is evaluated only on an explicit quadratic curve;
there is no unknown trajectory in the numerical premise. -/
theorem continuation_quadratic_deficit {lam anchor b C : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : zStart≤anchor) (hab : anchor≤b) (hb : b≤zEnd) (hC : 0≤C)
    (hinit : Y anchor=quadratic lam anchor-d.S)
    (hcheck : ∀ r ∈ Ico anchor b,∀ v ∈ controlFeatureSupport d,
      lam-r-2*C*(r-anchor)≤
        -featureTheta lam d v*(r-lam)-featureAlpha lam d v*
          (quadratic lam (r-v.1.1)-d.S-(quadratic lam r-d.S-C*(r-anchor)^2))) :
    ∀ r ∈ Icc anchor b,quadratic lam r-d.S-Y r≤C*(r-anchor)^2 := by
  let Q : ℝ → ℝ := fun r => quadratic lam r-d.S-C*(r-anchor)^2
  have hQd (r : ℝ) : HasDerivAt Q (lam-r-2*C*(r-anchor)) r := by
    convert! ((quadratic_hasDerivAt lam r).sub_const d.S).sub
      ((((hasDerivAt_id r).sub_const anchor).pow 2).const_mul C) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one]; ring)
  have hsub : ∀ r ∈ Ico anchor b,lam-r-2*C*(r-anchor)≤vectorField lam d r (Q r) := by
    intro r hr
    unfold vectorField
    apply le_min
    · nlinarith only [mul_nonneg hC (sub_nonneg.mpr hr.1)]
    · obtain ⟨v,hv,hval⟩ := hd.essInf_attained_in_featureSupport r (Q r)
      rw [←hval,featureH_as_highAffineControl hd hv Q r]
      exact hcheck r hr v hv
  have hh := scalar_ode_comparison (vectorField lam d) (19/2) Q Y
    (fun r => lam-r-2*C*(r-anchor)) (fun r => vectorField lam d r (Y r)) anchor b
    (fun r _ => hd.vectorField_lipschitz r)
    (continuous_iff_continuousAt.mpr (fun r => (hQd r).continuousAt)).continuousOn
    ((continuation_continuous hY).mono (Icc_subset_Icc ha hb))
    (fun r _ => (hQd r).hasDerivWithinAt)
    (fun r hr => hY.right_derivative ⟨ha.trans hr.1,hr.2.trans_le hb⟩)
    hsub (fun _ _ => le_rfl) (by dsimp [Q]; rw [hinit]; simp)
  intro r hr
  have hx := hh r hr
  dsimp [Q] at hx
  linarith only [hx]

/-- The initial line segment and the quadratic comparison combine into the
positive-part bound actually used by the head-barrier finite checks. -/
theorem continuation_quadratic_deficit_from_line {lam anchor b C : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (hd : Admissible lam d) (hY : IsContinuation lam d Y)
    (ha : zStart≤anchor) (hab : anchor≤b) (hb : b≤zEnd) (hC : 0≤C)
    (hline : ∀ r ∈ Icc zStart anchor,Y r=quadratic lam r-d.S)
    (hcheck : ∀ r ∈ Ico anchor b,∀ v ∈ controlFeatureSupport d,
      lam-r-2*C*(r-anchor)≤
        -featureTheta lam d v*(r-lam)-featureAlpha lam d v*
          (quadratic lam (r-v.1.1)-d.S-(quadratic lam r-d.S-C*(r-anchor)^2))) :
    ∀ r ∈ Icc zStart b,quadratic lam r-d.S-Y r≤C*(max (r-anchor) 0)^2 := by
  have hh := continuation_quadratic_deficit hd hY ha hab hb hC (hline anchor ⟨ha,le_rfl⟩) hcheck
  intro r hr
  by_cases hra : r≤anchor
  · rw [hline r ⟨hr.1,hra⟩,sub_self,max_eq_right (sub_nonpos.mpr hra)]
    simp
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hra))]
    exact hh r ⟨le_of_not_ge hra,hr.2⟩

end OptimalG.Variational
