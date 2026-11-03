import OptimalG.VariationalRecovery
import Mathlib.Analysis.Calculus.Deriv.Inv
import OptimalG.PolynomialCompletion
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The exact tangency equations used to attach the quadratic tail. -/
namespace OptimalG.Variational
open Set

noncomputable def capScore (lam S q : ℝ) : ℝ := lam / 2 - lam * S / (1 - q) ^ 2
noncomputable def capSlack (lam S q : ℝ) : ℝ := lam - q - capScore lam S q
noncomputable def capDeficit (lam S q : ℝ) : ℝ := S - quadratic lam q + cap lam S q

theorem cap_hasDerivAt (lam S q : ℝ) (hq : q ≠ 1) : HasDerivAt (cap lam S) (capScore lam S q) q := by
  have hh : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hi := hasDerivAt_id q
  have hd := (((hi.const_mul lam).div_const 2).const_add (lam ^ 2 - lam / 2)).sub
    ((hasDerivAt_const q (lam * S)).div ((hasDerivAt_const q 1).sub hi) hh)
  have heq : lam * 1 / 2 - (0 * (1 - q) - lam * S * (0 - 1)) / (1 - q) ^ 2 = capScore lam S q := by
    simp [capScore]
  change HasDerivAt (cap lam S) (lam * 1 / 2 - (0 * (1 - q) - lam * S * (0 - 1)) / (1 - q) ^ 2) q at hd
  rw [heq] at hd
  exact hd

/-- The two-class barrier rewritten in terms of deficit and distance to rank one. -/
theorem terminalBound_backward (lam S z q : ℝ) (hq : lam ≠ q) :
    terminalBound lam S z q = z * ((1 - z) - ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q)) := by
  have hh : lam - q ≠ 0 := sub_ne_zero.mpr hq
  unfold terminalBound capDeficit quadratic
  field_simp
  ring


theorem terminalBound_z_hasDerivAt (lam S z q : ℝ) (hq : lam ≠ q) :
    HasDerivAt (fun t => terminalBound lam S t q)
      (1 - 2 * z - ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q) +
        z * (1 - z) / (lam - q)) z := by
  have hh : lam - q ≠ 0 := sub_ne_zero.mpr hq
  have hc := (quadratic_hasDerivAt lam (1 - z + q)).comp z
    (((hasDerivAt_const z 1).sub (hasDerivAt_id z)).add_const q)
  have hd := ((hasDerivAt_id z).mul ((hc.sub_const S).sub_const (cap lam S q))).div_const (lam - q)
  have heq : (1 * (quadratic lam (1 - z + q) - S - cap lam S q) +
      z * ((lam - (1 - z + q)) * (0 - 1))) / (lam - q) =
      1 - 2 * z - ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q) +
        z * (1 - z) / (lam - q) := by
    unfold capDeficit quadratic
    field_simp
    ring
  change HasDerivAt (fun t => terminalBound lam S t q)
    ((1 * (quadratic lam (1 - z + q) - S - cap lam S q) +
      z * ((lam - (1 - z + q)) * (0 - 1))) / (lam - q)) z at hd
  rw [heq] at hd
  exact hd

theorem terminalBound_q_hasDerivAt (lam S z q : ℝ) (hq : lam ≠ q) (hq1 : q ≠ 1) :
    HasDerivAt (terminalBound lam S z)
      (z * ((lam - q) * capSlack lam S q - ((1 - z) ^ 2 / 2 + capDeficit lam S q)) /
        (lam - q) ^ 2) q := by
  have hh : lam - q ≠ 0 := sub_ne_zero.mpr hq
  have hc := (quadratic_hasDerivAt lam (1 - z + q)).comp q
    ((hasDerivAt_id q).const_add (1 - z))
  have hd := (((hc.sub_const S).sub (cap_hasDerivAt lam S q hq1)).const_mul z).div
    ((hasDerivAt_const q lam).sub (hasDerivAt_id q)) hh
  have heq : (z * ((lam - (1 - z + q)) * 1 - capScore lam S q) * (lam - q) -
      z * (quadratic lam (1 - z + q) - S - cap lam S q) * (0 - 1)) / (lam - q) ^ 2 =
      z * ((lam - q) * capSlack lam S q - ((1 - z) ^ 2 / 2 + capDeficit lam S q)) /
        (lam - q) ^ 2 := by
    unfold capSlack capDeficit quadratic
    ring
  change HasDerivAt (terminalBound lam S z)
    ((z * ((lam - (1 - z + q)) * 1 - capScore lam S q) * (lam - q) -
      z * (quadratic lam (1 - z + q) - S - cap lam S q) * (0 - 1)) / (lam - q) ^ 2) q at hd
  rw [heq] at hd
  exact hd

/-- Both first-order equations follow from an actual interior contact of the feasible barrier. -/
theorem interior_contact_equations (lam S z q A B C D H : ℝ) (Y : ℝ → ℝ)
    (hz : z ∈ Ioo A B) (hq : q ∈ Ioo C D) (hlq : lam ≠ q) (hq1 : q ≠ 1)
    (hfeasible : ∀ t ∈ Icc A B, ∀ r ∈ Icc C D, terminalBound lam S t r ≤ Y t)
    (hcontact : Y z = terminalBound lam S z q) (hY : HasDerivAt Y H z) :
    z * ((lam - q) * capSlack lam S q - ((1 - z) ^ 2 / 2 + capDeficit lam S q)) /
        (lam - q) ^ 2 = 0 ∧
    H = 1 - 2 * z - ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q) +
      z * (1 - z) / (lam - q) := by
  have hqmax : IsMaxOn (terminalBound lam S z) (Icc C D) q := by
    intro r hr
    rw [← hcontact]
    exact hfeasible z ⟨hz.1.le, hz.2.le⟩ r hr
  have hzmin : IsMinOn (fun t => Y t - terminalBound lam S t q) (Icc A B) z := by
    intro t ht
    change Y z - terminalBound lam S z q ≤ Y t - terminalBound lam S t q
    rw [hcontact, sub_self]
    exact sub_nonneg.mpr (hfeasible t ht q ⟨hq.1.le, hq.2.le⟩)
  have hqe := (hqmax.isLocalMax (Icc_mem_nhds hq.1 hq.2)).hasDerivAt_eq_zero
    (terminalBound_q_hasDerivAt lam S z q hlq hq1)
  have hze := (hzmin.isLocalMin (Icc_mem_nhds hz.1 hz.2)).hasDerivAt_eq_zero
    (hY.sub (terminalBound_z_hasDerivAt lam S z q hlq))
  exact ⟨hqe, sub_eq_zero.mp hze⟩

/-- Equations C.8 from the two interior tangencies. -/
theorem tail_contact_identities (lam S z q Y H : ℝ) (hq : lam ≠ q) (hz : z ≠ 0)
    (hvalue : Y = terminalBound lam S z q)
    (hqcrit : z * ((lam - q) * capSlack lam S q - ((1 - z) ^ 2 / 2 + capDeficit lam S q)) /
        (lam - q) ^ 2 = 0)
    (hzcrit : H = 1 - 2 * z - ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q) +
      z * (1 - z) / (lam - q)) :
    (1 - z) ^ 2 = 2 * (lam - q) * capSlack lam S q - 2 * capDeficit lam S q ∧
    Y = z * ((1 - z) - capSlack lam S q) ∧
    H = 1 - 2 * z - capSlack lam S q + z * (1 - z) / (lam - q) := by
  have hh : lam - q ≠ 0 := sub_ne_zero.mpr hq
  have hnum := (div_eq_zero_iff.mp hqcrit).resolve_right (pow_ne_zero 2 hh)
  have heq := (mul_eq_zero.mp hnum).resolve_left hz
  have hfrac : ((1 - z) ^ 2 / 2 + capDeficit lam S q) / (lam - q) = capSlack lam S q := by
    apply (div_eq_iff hh).mpr
    nlinarith
  refine ⟨by nlinarith, ?_, ?_⟩
  · rw [hvalue, terminalBound_backward lam S z q hq, hfrac]
  · simpa only [hfrac] using hzcrit

end OptimalG.Variational
