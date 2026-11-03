import OptimalG.ElectionOneLimit

/-!
# Replicating rational voter weights

A natural multiplicity for each ranking gives an actual finite election with
uniform voters. The exact averaging identity below transports stability and
strict distortion violations; it does not assume their realizability.
-/

namespace OptimalG
open Set MeasureTheory Filter
open scoped BigOperators Topology

abbrev VoterCopies {V : Type*} (copies : V → ℕ) := (v : V) × Fin (copies v)

theorem voterCopies_card {V : Type*} [Fintype V] (copies : V → ℕ) :
    Fintype.card (VoterCopies copies) = ∑ v, copies v := by
  simp [VoterCopies, Fintype.card_sigma]

noncomputable def copyWeight {V : Type*} [Fintype V] (copies : V → ℕ) (v : V) : ℝ :=
  (copies v : ℝ) / (∑ t, copies t)

theorem copyWeight_nonneg {V : Type*} [Fintype V] (copies : V → ℕ) (v : V) :
    0 ≤ copyWeight copies v := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem copyWeight_total {V : Type*} [Fintype V] (copies : V → ℕ)
    (hcopies : 0 < ∑ v, copies v) : ∑ v, copyWeight copies v = 1 := by
  have hn : ((∑ v, copies v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcopies
  simp only [copyWeight, ← Finset.sum_div, ← Nat.cast_sum]
  exact div_self hn

noncomputable abbrev replicatedElection {V : Type*} [Fintype V] {m : ℕ}
    (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (copies : V → ℕ) (hcopies : 0 < ∑ v, copies v) : Election := by
  letI : Nonempty (VoterCopies copies) := Fintype.card_pos_iff.mp (by
    simpa only [voterCopies_card] using hcopies)
  exact profileElection hm (fun v : VoterCopies copies => orders v.1)

theorem copied_average {V : Type*} [Fintype V] (copies : V → ℕ) (f : V → ℝ) :
    (∑ v : VoterCopies copies, f v.1) / Fintype.card (VoterCopies copies) =
      expectation (copyWeight copies) f := by
  rw [voterCopies_card]
  simp only [VoterCopies, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, expectation, copyWeight, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- The full uniform profile average can be reindexed to the weighted original
profile, for any real observable of its ranking. -/
theorem replicatedElection_average {V : Type*} [Fintype V] {m : ℕ}
    (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (copies : V → ℕ) (hcopies : 0 < ∑ v, copies v)
    (f : Equiv.Perm (Fin m) → ℝ) :
    expectation (replicatedElection hm orders copies hcopies).voterWeight
      (fun v => f ((replicatedElection hm orders copies hcopies).order v)) =
      expectation (copyWeight copies) (fun v => f (orders v)) := by
  letI : Nonempty (VoterCopies copies) := Fintype.card_pos_iff.mp (by
    simpa only [voterCopies_card] using hcopies)
  change (∑ i : Fin (Fintype.card (VoterCopies copies)),
    (1 / (Fintype.card (VoterCopies copies) : ℝ)) *
      f (orders (((Fintype.equivFin (VoterCopies copies)).symm i).1))) = _
  rw [← Finset.mul_sum]
  rw [Equiv.sum_comp (Fintype.equivFin (VoterCopies copies)).symm
    (fun v : VoterCopies copies => f (orders v.1))]
  have h := copied_average copies (fun v => f (orders v))
  convert h using 1; ring

/-- Exact stability transfer when the weights have a common natural denominator. -/
theorem replicatedElection_stable {V : Type*} [Fintype V] {m : ℕ}
    (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (copies : V → ℕ) (hcopies : 0 < ∑ v, copies v)
    (g : ℝ → ℝ) (D : Lottery m)
    (hstable : ∀ a, expectation (copyWeight copies)
      (fun v => orderedActivation g D.weight (orders v) a) ≤ ∫ r in (0 : ℝ)..1, g r) :
    (replicatedElection hm orders copies hcopies).Stable g D := by
  intro a
  change expectation _ (fun v => orderedActivation g D.weight
    ((replicatedElection hm orders copies hcopies).order v) a) ≤ _
  exact (replicatedElection_average hm orders copies hcopies
    (fun order => orderedActivation g D.weight order a)).trans_le (hstable a)

/-- A strict weighted violation with rational voter weights produces an actual
finite equal-voter distortion witness, with a genuine separated metric. -/
theorem replicatedElection_witnessAbove {V : Type*} [Fintype V] {m : ℕ} [NeZero m]
    (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (copies : V → ℕ) (hcopies : 0 < ∑ v, copies v)
    (g : ℝ → ℝ) (D : Lottery m) (rho : Fin m → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (a : Fin m) (ha : rho a = 0)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hstable : ∀ a, expectation (copyWeight copies)
      (fun v => orderedActivation g D.weight (orders v) a) ≤ ∫ r in (0 : ℝ)..1, g r)
    (hexcess : lam * expectation (copyWeight copies)
      (fun v => maximumGap (fun a => ((orders v).symm a).val) rho) <
      expectation (copyWeight copies)
        (fun v => expectation D.weight (runningMin (fun a => ((orders v).symm a).val) rho))) :
    WitnessAbove g (1 + 2 * lam) := by
  let E := replicatedElection hm orders copies hcopies
  have hviolation : lam * expectation E.voterWeight
      (fun v => maximumGap (E.ordinalRank v) rho) <
      expectation E.voterWeight (fun v => expectation D.weight (runningMin (E.ordinalRank v) rho)) := by
    change lam * expectation E.voterWeight
      (fun v => maximumGap (fun a => ((E.order v).symm a).val) rho) <
      expectation E.voterWeight (fun v => expectation D.weight
        (runningMin (fun a => ((E.order v).symm a).val) rho))
    have hG := replicatedElection_average hm orders copies hcopies
      (fun order => maximumGap (fun a => (order.symm a).val) rho)
    have hN := replicatedElection_average hm orders copies hcopies
      (fun order => expectation D.weight (runningMin (fun a => (order.symm a).val) rho))
    calc
      _ = lam * expectation (copyWeight copies)
          (fun v => maximumGap (fun a => ((orders v).symm a).val) rho) := congrArg (lam * ·) hG
      _ < expectation (copyWeight copies) (fun v => expectation D.weight
          (runningMin (fun a => ((orders v).symm a).val) rho)) := hexcess
      _ = _ := hN.symm
  obtain ⟨metric, hconsistent, _hminimal, hpositive, hratio⟩ :=
    exists_metric_of_strict_runningMin_violation E.ordinalRank rho E.voterWeight D.weight lam
      hrho E.voterWeight_nonneg E.voterWeight_total D.total hlam a ha hviolation
  refine ⟨E, D, replicatedElection_stable hm orders copies hcopies g D hstable,
    metric.toPseudoMetricSpace, hconsistent, a, hpositive, ?_⟩
  rw [Election.lotteryCost_eq_voter_average]
  exact (lt_div_iff₀ hpositive).mp hratio

/-- Natural multiplicities approximating an arbitrary finite probability vector. -/
noncomputable def gridCopies {V : Type*} (w : V → ℝ) (n : ℕ) (v : V) : ℕ :=
  ⌊((n + 1 : ℕ) : ℝ) * w v⌋₊

theorem gridCopies_weight_eq {V : Type*} [Fintype V] (w : V → ℝ) (n : ℕ) (v : V) :
    copyWeight (gridCopies w n) v = lowerGrid n (w v) / ∑ t, lowerGrid n (w t) := by
  simp only [copyWeight, gridCopies, lowerGrid, ← Finset.sum_div, ← Nat.cast_sum]
  have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem gridCopies_tendsto {V : Type*} [Fintype V] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hsum : ∑ v, w v = 1) :
    Tendsto (fun n => copyWeight (gridCopies w n)) atTop (𝓝 w) := by
  apply tendsto_pi_nhds.mpr
  intro v
  have hden : Tendsto (fun n => ∑ t, lowerGrid n (w t)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hsum] using tendsto_finsetSum Finset.univ (fun t _ => lowerGrid_tendsto (w t) (hw t))
  have hquot := (lowerGrid_tendsto (w v) (hw v)).div hden (by norm_num)
  change Tendsto (fun n => lowerGrid n (w v) / ∑ t, lowerGrid n (w t)) atTop (𝓝 (w v / 1)) at hquot
  simpa only [gridCopies_weight_eq, div_one] using hquot

theorem gridCopies_eventually_nonempty {V : Type*} [Fintype V] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hsum : ∑ v, w v = 1) :
    ∀ᶠ n in atTop, 0 < ∑ v, gridCopies w n v := by
  have hden : Tendsto (fun n => ∑ t, lowerGrid n (w t)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hsum] using tendsto_finsetSum Finset.univ (fun t _ => lowerGrid_tendsto (w t) (hw t))
  filter_upwards [hden.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)] with n hn
  have hdenpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have heq : (∑ t, lowerGrid n (w t)) = ((∑ t, gridCopies w n t : ℕ) : ℝ) / (n + 1 : ℕ) := by
    simp only [gridCopies, lowerGrid, Nat.cast_sum, Finset.sum_div]
  rw [heq] at hn
  have hnum : (0 : ℝ) < ((∑ t, gridCopies w n t : ℕ) : ℝ) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge (le_of_lt hdenpos) h.2))
  exact_mod_cast hnum

/-- Every neighborhood of a probability vector contains a rational probability
vector represented by an actual nonempty finite list of voters. -/
theorem exists_copyWeight_mem_nhds {V : Type*} [Fintype V] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hsum : ∑ v, w v = 1)
    (U : Set (V → ℝ)) (hU : U ∈ 𝓝 w) :
    ∃ copies : V → ℕ, 0 < ∑ v, copies v ∧ copyWeight copies ∈ U := by
  obtain ⟨n, hn, hmem⟩ := ((gridCopies_eventually_nonempty w hw hsum).and
    ((gridCopies_tendsto w hw hsum).eventually hU)).exists
  exact ⟨gridCopies w n, hn, hmem⟩

end OptimalG
