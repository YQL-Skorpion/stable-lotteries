import OptimalG.LowerElection

/-!
# Finite rank-grid realizations for Election 1

There are n equal-mass supported candidates and one unsupported reference.
Its position k gives rank k/n exactly. Each base ranking is symmetrized by
all n! supported-candidate permutations, while the reference stays fixed.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

/-- Extend a permutation by fixing the additional `none` point. -/
def optionPermutationHom (H : Type*) : Equiv.Perm H →* Equiv.Perm (Option H) where
  toFun sigma := sigma.optionCongr
  map_one' := by ext a; cases a <;> rfl
  map_mul' sigma tau := by ext a; cases a <;> rfl

/-- Permute the n supported labels while fixing label n. -/
def electionOneAction (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin (n + 1)) :=
  ((finSuccEquiv' (Fin.last n)).symm.permCongrHom).toMonoidHom.comp
    (optionPermutationHom (Fin n))

@[simp] theorem electionOneAction_last (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    electionOneAction n sigma (Fin.last n) = Fin.last n := by
  simp [electionOneAction, optionPermutationHom, Equiv.permCongrHom,
    Equiv.permCongr_apply]

@[simp] theorem electionOneAction_castSucc {n : ℕ} (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    electionOneAction n sigma i.castSucc = (sigma i).castSucc := by
  simp [electionOneAction, optionPermutationHom, Equiv.permCongrHom,
    Equiv.permCongr_apply, finSuccEquiv', Fin.succAbove_last]

/-- The original ranking places the unsupported label n at ordinal position k. -/
def electionOneOrder {n : ℕ} (k : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' k).trans (finSuccEquiv' (Fin.last n)).symm

@[simp] theorem electionOneOrder_at {n : ℕ} (k : Fin (n + 1)) :
    electionOneOrder k k = Fin.last n := by simp [electionOneOrder]

@[simp] theorem electionOneOrder_symm_last {n : ℕ} (k : Fin (n + 1)) :
    (electionOneOrder k).symm (Fin.last n) = k := by simp [electionOneOrder]

/-- The finite uniform lottery on the n supported candidates. -/
noncomputable def electionOneLottery (n : ℕ) (hn : 0 < n) : Lottery (n + 1) where
  weight i := if i = Fin.last n then 0 else 1 / n
  nonneg i := by split_ifs; rfl; exact div_nonneg (by norm_num) (Nat.cast_nonneg n)
  total := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_ne_last, hn0]

@[simp] theorem electionOneLottery_last (n : ℕ) (hn : 0 < n) :
    (electionOneLottery n hn).weight (Fin.last n) = 0 := by simp [electionOneLottery]

@[simp] theorem electionOneLottery_castSucc (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (electionOneLottery n hn).weight i.castSucc = 1 / n := by
  simp [electionOneLottery, Fin.castSucc_ne_last]

theorem electionOneLottery_eq_zero_iff (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) :
    (electionOneLottery n hn).weight i = 0 ↔ i = Fin.last n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp [electionOneLottery, hn0]

theorem electionOneLottery_invariant (n : ℕ) (hn : 0 < n)
    (sigma : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    (electionOneLottery n hn).weight (electionOneAction n sigma i) =
      (electionOneLottery n hn).weight i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

theorem electionOneAction_transitive (n : ℕ) (hn : 0 < n)
    (a b : Fin (n + 1))
    (ha : (electionOneLottery n hn).weight a ≠ 0)
    (hb : (electionOneLottery n hn).weight b ≠ 0) :
    ∃ sigma, electionOneAction n sigma a = b := by
  have haLast : a ≠ Fin.last n := by
    intro h
    exact ha (h ▸ electionOneLottery_last n hn)
  have hbLast : b ≠ Fin.last n := by
    intro h
    exact hb (h ▸ electionOneLottery_last n hn)
  let i : Fin n := ⟨a.val, Fin.lt_last_iff_ne_last.mpr haLast⟩
  let j : Fin n := ⟨b.val, Fin.lt_last_iff_ne_last.mpr hbLast⟩
  have hi : i.castSucc = a := Fin.ext rfl
  have hj : j.castSucc = b := Fin.ext rfl
  refine ⟨Equiv.swap i j, ?_⟩
  rw [← hi, ← hj]
  simp

/-- Before the reference position, every slot has mass 1/n. -/
theorem electionOne_rankCut (n : ℕ) (hn : 0 < n) (k : Fin (n + 1)) :
    rankCut (fun i => (electionOneLottery n hn).weight (electionOneOrder k i)) k.val =
      (k.val : ℝ) / n := by
  have hpoint : ∀ i : Fin (n + 1),
      (if i.val < k.val then (electionOneLottery n hn).weight (electionOneOrder k i) else 0) =
      (if i < k then (1 : ℝ) / n else 0) := by
    intro i
    by_cases hik : i < k
    · have hne : electionOneOrder k i ≠ Fin.last n := by
        intro h
        have hieq := (electionOneOrder k).injective (h.trans (electionOneOrder_at k).symm)
        exact (ne_of_lt hik) hieq
      simp [hik, electionOneLottery, hne]
    · simp [hik]
  unfold rankCut
  simp_rw [hpoint]
  have hfilter : Finset.univ.filter (fun i : Fin (n + 1) => i < k) = Finset.Iio k := by
    ext i
    simp
  rw [← Finset.sum_filter, hfilter]
  simp [Fin.card_Iio, nsmul_eq_mul, div_eq_mul_inv]

/-- The unsupported candidate's activation is exactly g(k/n). -/
theorem electionOne_reference_activation (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (g : ℝ → ℝ) :
    orderedActivation g (electionOneLottery n hn).weight (electionOneOrder k) (Fin.last n) =
      g ((k.val : ℝ) / n) := by
  unfold orderedActivation
  rw [electionOneOrder_symm_last]
  rw [rankActivation_of_mass_zero]
  · rw [electionOne_rankCut]
  · simp

/-- Height zero at the reference and one at every supported candidate. -/
def singleZeroHeight {C : Type*} [DecidableEq C] (a : C) (b : C) : ℝ :=
  if b = a then 0 else 1

theorem singleZeroHeight_nonneg {C : Type*} [DecidableEq C] (a b : C) :
    0 ≤ singleZeroHeight a b := by unfold singleZeroHeight; split_ifs <;> norm_num

theorem singleZeroHeight_le_one {C : Type*} [DecidableEq C] (a b : C) :
    singleZeroHeight a b ≤ 1 := by unfold singleZeroHeight; split_ifs <;> norm_num

/-- Election 1's running minimum has an exact binary form, including at the
zero-mass reference itself. -/
theorem runningMin_singleZero {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (rank : C → ℕ) (a b : C) :
    runningMin rank (singleZeroHeight a) b = if rank b < rank a then 1 else 0 := by
  by_cases hba : rank b < rank a
  · rw [if_pos hba]
    have hbne : b ≠ a := by intro h; subst b; omega
    apply le_antisymm
    · simpa only [singleZeroHeight, if_neg hbne] using runningMin_le_self rank (singleZeroHeight a) b
    · apply Finset.le_inf'
      intro c _
      split_ifs with hcb
      · have hcne : c ≠ a := by intro h; subst c; omega
        simp [singleZeroHeight, hcne]
      · simp [singleZeroHeight, hbne]
  · rw [if_neg hba]
    apply le_antisymm
    · have h := runningMin_le_of_rank_le rank (singleZeroHeight a) b a (by omega)
      simpa [singleZeroHeight] using h
    · exact runningMin_nonneg rank (singleZeroHeight a) (singleZeroHeight_nonneg a) b

theorem maximumGap_singleZero_le_one {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (rank : C → ℕ) (a : C) : maximumGap rank (singleZeroHeight a) ≤ 1 := by
  apply Finset.sup'_le
  intro b _
  have h1 := singleZeroHeight_le_one a b
  have h2 := runningMin_nonneg rank (singleZeroHeight a) (singleZeroHeight_nonneg a) b
  linarith

theorem maximumGap_singleZero_top {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (rank : C → ℕ) (a : C) (htop : ∀ b, b ≠ a → rank b < rank a) :
    maximumGap rank (singleZeroHeight a) = 0 := by
  apply Finset.sup'_eq_of_forall
  intro b _
  rw [runningMin_singleZero]
  by_cases hba : b = a
  · subst b
    simp [singleZeroHeight]
  · simp [singleZeroHeight, hba, htop b hba]

theorem maximumGap_singleZero_above {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (rank : C → ℕ) (a b : C) (hba : b ≠ a) (hab : rank a ≤ rank b) :
    maximumGap rank (singleZeroHeight a) = 1 := by
  apply le_antisymm (maximumGap_singleZero_le_one rank a)
  have h := le_maximumGap rank (singleZeroHeight a) b
  simpa [runningMin_singleZero, singleZeroHeight, hba, not_lt.mpr hab] using h

/-- The expected running minimum is exactly the lottery mass before the reference. -/
theorem runningMin_singleZero_mass {n : ℕ} (order : Equiv.Perm (Fin (n + 1)))
    (D : Fin (n + 1) → ℝ) (a : Fin (n + 1)) :
    expectation D (runningMin (fun b => (order.symm b).val) (singleZeroHeight a)) =
      rankCut (fun i => D (order i)) (order.symm a).val := by
  unfold expectation
  rw [← Equiv.sum_comp order (fun b => D b *
    runningMin (fun b => (order.symm b).val) (singleZeroHeight a) b)]
  simp only [runningMin_singleZero, Equiv.symm_apply_apply, mul_ite, mul_one, mul_zero, rankCut]

/-- The gap is zero exactly when the reference occupies the top ordinal position. -/
theorem maximumGap_singleZero_order {n : ℕ} (order : Equiv.Perm (Fin (n + 1)))
    (a : Fin (n + 1)) :
    maximumGap (fun b => (order.symm b).val) (singleZeroHeight a) =
      if order.symm a = Fin.last n then 0 else 1 := by
  by_cases htop : order.symm a = Fin.last n
  · rw [if_pos htop]
    apply maximumGap_singleZero_top
    intro b hba
    rw [htop]
    apply Fin.lt_last_iff_ne_last.mpr
    intro hbtop
    exact hba (order.symm.injective (hbtop.trans htop.symm))
  · rw [if_neg htop]
    apply maximumGap_singleZero_above _ a (order (Fin.last n))
    · intro heq
      have h := congrArg order.symm heq
      simp only [Equiv.symm_apply_apply] at h
      exact htop h.symm
    · simp only [Equiv.symm_apply_apply]
      exact Nat.le_of_lt_succ (order.symm a).isLt

/-- Repeated supported permutations leave the reference at exactly position k. -/
theorem electionOne_symmetrized_reference_position (n : ℕ) (k : Fin (n + 1))
    (sigma : Equiv.Perm (Fin n)) :
    ((electionOneOrder k).trans (electionOneAction n sigma)).symm (Fin.last n) = k := by
  apply ((electionOneOrder k).trans (electionOneAction n sigma)).injective
  simp

/-- Every voter type at rank k/n has numerator k/n exactly. -/
theorem electionOne_runningMin_mass (n : ℕ) (hn : 0 < n) (k : Fin (n + 1))
    (sigma : Equiv.Perm (Fin n)) :
    expectation (electionOneLottery n hn).weight
      (runningMin (fun b => (((electionOneOrder k).trans (electionOneAction n sigma)).symm b).val)
        (singleZeroHeight (Fin.last n))) = (k.val : ℝ) / n := by
  rw [runningMin_singleZero_mass, electionOne_symmetrized_reference_position]
  have hweights : (fun i => (electionOneLottery n hn).weight
      (((electionOneOrder k).trans (electionOneAction n sigma)) i)) =
        fun i => (electionOneLottery n hn).weight (electionOneOrder k i) := by
    funext i
    exact electionOneLottery_invariant n hn sigma _
  rw [hweights]
  exact electionOne_rankCut n hn k

/-- Every voter type below rank 1 has gap one, and the top type has gap zero. -/
theorem electionOne_maximumGap (n : ℕ) (k : Fin (n + 1)) (sigma : Equiv.Perm (Fin n)) :
    maximumGap
      (fun b => (((electionOneOrder k).trans (electionOneAction n sigma)).symm b).val)
      (singleZeroHeight (Fin.last n)) = if k = Fin.last n then 0 else 1 := by
  rw [maximumGap_singleZero_order, electionOne_symmetrized_reference_position]

/-- The finite Election 1 profile: a finite list of rank-grid positions and
all supported-candidate permutations for each list entry. -/
noncomputable def electionOneFinite {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (ranks : T → Fin (n + 1)) : Election :=
  mixedSymmetrizedElection (Nat.succ_pos n) (fun t => electionOneOrder (ranks t))
    (electionOneAction n)

/-- Exact stability for finite Election 1. The condition is precisely the
uniform finite average of g evaluated at the requested rational ranks. -/
theorem electionOneFinite_stable {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (hn : 0 < n) (ranks : T → Fin (n + 1)) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 1))
    (haverage : (∑ t : T, g (((ranks t).val : ℝ) / n)) / Fintype.card T ≤
      ∫ r in (0 : ℝ)..1, g r) :
    (electionOneFinite n ranks).Stable g (electionOneLottery n hn) := by
  apply one_orbit_mixed_election_stable (Nat.succ_pos n)
    (fun t => electionOneOrder (ranks t)) (electionOneAction n) g (electionOneLottery n hn)
    hg (electionOneLottery_invariant n hn) (electionOneAction_transitive n hn)
  · intro a ha sigma
    have heq := (electionOneLottery_eq_zero_iff n hn a).mp ha
    subst a
    exact electionOneAction_last n sigma
  · intro a ha
    have heq := (electionOneLottery_eq_zero_iff n hn a).mp ha
    subst a
    simp_rw [electionOne_reference_activation]
    exact haverage

/-- In a finite product profile, repeating every type once per group element
leaves the uniform average over types unchanged. -/
theorem mixedProfile_mean {T G : Type*} [Fintype T] [Nonempty T]
    [Fintype G] [Group G] {m : ℕ} (hm : 0 < m)
    (orders : T → Equiv.Perm (Fin m)) (action : G →* Equiv.Perm (Fin m))
    (f : T → ℝ) :
    expectation (mixedSymmetrizedElection hm orders action).voterWeight
      (fun v => f ((Fintype.equivFin (T × G)).symm v).1) =
        (∑ t : T, f t) / Fintype.card T := by
  change (∑ i : Fin (Fintype.card (T × G)), (1 / (Fintype.card (T × G) : ℝ)) *
    f ((Fintype.equivFin (T × G)).symm i).1) = _
  rw [← Finset.mul_sum]
  have hsum := Equiv.sum_comp (Fintype.equivFin (T × G)).symm (fun v : T × G => f v.1)
  rw [hsum]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul, ← Finset.mul_sum]
  have hT : (Fintype.card T : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Fintype.card_pos (α := T))
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Fintype.card_pos (α := G))
  field_simp

/-- The finite profile numerator is the exact arithmetic mean of its ranks. -/
theorem electionOneFinite_numerator {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (hn : 0 < n) (ranks : T → Fin (n + 1)) :
    expectation (electionOneFinite n ranks).voterWeight
      (fun v => expectation (electionOneLottery n hn).weight
        (runningMin ((electionOneFinite n ranks).ordinalRank v)
          (singleZeroHeight (Fin.last n)))) =
      (∑ t : T, ((ranks t).val : ℝ) / n) / Fintype.card T := by
  have hpoint : (fun v : (electionOneFinite n ranks).Voter =>
      expectation (electionOneLottery n hn).weight
        (runningMin ((electionOneFinite n ranks).ordinalRank v)
          (singleZeroHeight (Fin.last n)))) =
      fun v => (((ranks ((Fintype.equivFin (T × Equiv.Perm (Fin n))).symm v).1).val : ℝ) / n) := by
    funext v
    exact electionOne_runningMin_mass n hn _ _
  rw [hpoint]
  exact mixedProfile_mean (T := T) (G := Equiv.Perm (Fin n)) (Nat.succ_pos n)
    (fun t => electionOneOrder (ranks t)) (electionOneAction n)
    (fun t => ((ranks t).val : ℝ) / n)

/-- The finite profile denominator is the fraction of its types below rank one. -/
theorem electionOneFinite_gap {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (ranks : T → Fin (n + 1)) :
    expectation (electionOneFinite n ranks).voterWeight
      (fun v => maximumGap ((electionOneFinite n ranks).ordinalRank v)
        (singleZeroHeight (Fin.last n))) =
      (∑ t : T, if ranks t = Fin.last n then (0 : ℝ) else 1) / Fintype.card T := by
  have hpoint : (fun v : (electionOneFinite n ranks).Voter =>
      maximumGap ((electionOneFinite n ranks).ordinalRank v) (singleZeroHeight (Fin.last n))) =
      fun v => if ranks ((Fintype.equivFin (T × Equiv.Perm (Fin n))).symm v).1 = Fin.last n
        then (0 : ℝ) else 1 := by
    funext v
    exact electionOne_maximumGap n _ _
  rw [hpoint]
  exact mixedProfile_mean (T := T) (G := Equiv.Perm (Fin n)) (Nat.succ_pos n)
    (fun t => electionOneOrder (ranks t)) (electionOneAction n)
    (fun t => if ranks t = Fin.last n then (0 : ℝ) else 1)

/-- A completely finite lower-bound witness whenever the two explicit rank-grid
averages satisfy the stability and excess-cost tests. -/
theorem electionOneFinite_witnessAbove {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (hn : 0 < n) (ranks : T → Fin (n + 1))
    (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hg : ContinuousOn g (Icc 0 1))
    (hactivation : (∑ t : T, g (((ranks t).val : ℝ) / n)) / Fintype.card T ≤
      ∫ r in (0 : ℝ)..1, g r)
    (hexcess : lam * ((∑ t : T, if ranks t = Fin.last n then (0 : ℝ) else 1) /
        Fintype.card T) < (∑ t : T, ((ranks t).val : ℝ) / n) / Fintype.card T) :
    WitnessAbove g (1 + 2 * lam) := by
  let E := electionOneFinite n ranks
  let D := electionOneLottery n hn
  have hviolation : lam * expectation E.voterWeight
      (fun v => maximumGap (E.ordinalRank v) (singleZeroHeight (Fin.last n))) <
      expectation E.voterWeight (fun v => expectation D.weight
        (runningMin (E.ordinalRank v) (singleZeroHeight (Fin.last n)))) := by
    rw [electionOneFinite_numerator, electionOneFinite_gap]
    exact hexcess
  obtain ⟨metric, hconsistent, _hminimal, hpositive, hratio⟩ :=
    exists_metric_of_strict_runningMin_violation E.ordinalRank (singleZeroHeight (Fin.last n))
      E.voterWeight D.weight lam (singleZeroHeight_nonneg (Fin.last n))
      E.voterWeight_nonneg E.voterWeight_total D.total hlam (Fin.last n)
      (by simp [singleZeroHeight]) hviolation
  refine ⟨E, D, electionOneFinite_stable n hn ranks g hg hactivation,
    metric.toPseudoMetricSpace, hconsistent, Fin.last n, hpositive, ?_⟩
  rw [Election.lotteryCost_eq_voter_average]
  exact (lt_div_iff₀ hpositive).mp hratio

/-- Necessary inequality for every finite rational-rank test distribution. -/
theorem electionOneFinite_necessary {T : Type*} [Fintype T] [Nonempty T]
    (n : ℕ) (hn : 0 < n) (ranks : T → Fin (n + 1))
    (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hg : ContinuousOn g (Icc 0 1)) (hbound : UniversalBound g (1 + 2 * lam))
    (hactivation : (∑ t : T, g (((ranks t).val : ℝ) / n)) / Fintype.card T ≤
      ∫ r in (0 : ℝ)..1, g r) :
    (∑ t : T, ((ranks t).val : ℝ) / n) / Fintype.card T ≤
      lam * ((∑ t : T, if ranks t = Fin.last n then (0 : ℝ) else 1) / Fintype.card T) := by
  by_contra h
  exact witnessAbove_not_universalBound g _
    (electionOneFinite_witnessAbove n hn ranks g lam hlam hg hactivation (lt_of_not_ge h)) hbound

end OptimalG
