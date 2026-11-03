import OptimalG.Election
import OptimalG.BiasedMetric

/-!
# Finite symmetrized election constructions

All averaging below is over a finite group of actual candidate permutations.
The resulting activation is exactly the expectation in the equally weighted
profile that contains one voter per group element. No continuum of candidates
or limiting voter weights is used in these symmetry results.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators

/-- Relabeling candidates commutes with activation when it preserves their
lottery weights. -/
theorem orderedActivation_relabel {C : Type*} {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C) (sigma : Equiv.Perm C)
    (hD : ∀ a, D (sigma a) = D a) (a : C) :
    orderedActivation g D (order.trans sigma) a =
      orderedActivation g D order (sigma.symm a) := by
  have hweights : (fun i => D ((order.trans sigma) i)) = fun i => D (order i) := by
    funext i
    exact hD (order i)
  unfold orderedActivation
  rw [hweights]
  rfl

/-- Average over the finite relabelings of one ranking. -/
noncomputable def symmetrizedActivation {C G : Type*} [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C) (a : C) : ℝ :=
  (∑ sigma : G, orderedActivation g D (order.trans (action sigma)) a) / Fintype.card G

/-- The finite symmetrized activation is constant on each group orbit. -/
theorem symmetrizedActivation_invariant {C G : Type*} [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C)
    (hD : ∀ sigma a, D (action sigma a) = D a) (tau : G) (a : C) :
    symmetrizedActivation g D order action (action tau a) =
      symmetrizedActivation g D order action a := by
  have hpoint : ∀ sigma : G,
      orderedActivation g D (order.trans (action (tau * sigma))) (action tau a) =
        orderedActivation g D (order.trans (action sigma)) a := by
    intro sigma
    have horder : order.trans (action (tau * sigma)) =
        (order.trans (action sigma)).trans (action tau) := by
      ext i
      simp only [Equiv.trans_apply, map_mul, Equiv.Perm.mul_apply]
    rw [horder, orderedActivation_relabel g D _ (action tau) (hD tau)]
    simp only [Equiv.symm_apply_apply]
  have hreindex := Equiv.sum_comp (Equiv.mulLeft tau)
    (fun sigma => orderedActivation g D (order.trans (action sigma)) (action tau a))
  change (∑ sigma : G, orderedActivation g D (order.trans (action (tau * sigma)))
    (action tau a)) = _ at hreindex
  simp_rw [hpoint] at hreindex
  exact congrArg (fun t : ℝ => t / Fintype.card G) hreindex.symm

/-- The symmetrized score is the actual finite voter expectation. -/
theorem symmetrizedActivation_eq_expectation
    {C G : Type*} [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C) (a : C) :
    symmetrizedActivation g D order action a =
      expectation (fun _ : G => (1 : ℝ) / Fintype.card G)
        (fun sigma => orderedActivation g D (order.trans (action sigma)) a) := by
  simp only [symmetrizedActivation, expectation, one_div, ← Finset.mul_sum]
  ring

/-- Finite symmetrization preserves the total rank-partition activation. -/
theorem symmetrized_partition {C G : Type*} [Fintype C] [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1) :
    expectation D (symmetrizedActivation g D order action) = ∫ r in (0 : ℝ)..1, g r := by
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Fintype.card_pos (α := G))
  have hw : ∑ _sigma : G, (1 : ℝ) / Fintype.card G = 1 := by simp [hcard]
  have hfun : symmetrizedActivation g D order action = fun a =>
      expectation (fun _ : G => (1 : ℝ) / Fintype.card G)
        (fun sigma => orderedActivation g D (order.trans (action sigma)) a) := by
    funext a
    exact symmetrizedActivation_eq_expectation g D order action a
  rw [hfun, expectation_commute]
  simp_rw [ordered_integral_partition g D _ hcont hD hsum]
  exact expectation_const hw _

/-- If a supported orbit's total activation equals its mass times the mean,
then every candidate in that orbit has exactly the mean activation. -/
theorem orbit_stationarity_of_balance {C G : Type*}
    [Fintype G] [Group G] [DecidableEq C] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C) (S : Finset C) (mean : ℝ)
    (hD : ∀ sigma a, D (action sigma a) = D a)
    (a : C) (horbit : ∀ b ∈ S, ∃ sigma, action sigma a = b)
    (hmass : 0 < ∑ b ∈ S, D b)
    (hbalance : ∑ b ∈ S, D b * symmetrizedActivation g D order action b =
      (∑ b ∈ S, D b) * mean) :
    symmetrizedActivation g D order action a = mean := by
  have hsame : ∀ b ∈ S, symmetrizedActivation g D order action b =
      symmetrizedActivation g D order action a := by
    intro b hb
    obtain ⟨sigma, rfl⟩ := horbit b hb
    exact symmetrizedActivation_invariant g D order action hD sigma a
  have heq : (∑ b ∈ S, D b) * symmetrizedActivation g D order action a =
      (∑ b ∈ S, D b) * mean := by
    calc
      _ = ∑ b ∈ S, D b * symmetrizedActivation g D order action a := by rw [Finset.sum_mul]
      _ = ∑ b ∈ S, D b * symmetrizedActivation g D order action b := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hsame b hb]
      _ = _ := hbalance
  exact (mul_left_cancel₀ (ne_of_gt hmass)) heq

/-- A completely symmetric profile makes every candidate stationary. This
is the supported-class part of Election 1. -/
theorem full_symmetry_stationary {C : Type*} [Fintype C] [Nonempty C]
    [DecidableEq C] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1)
    (huniform : ∀ a b, D a = D b) (a : C) :
    symmetrizedActivation g D order (MonoidHom.id (Equiv.Perm C)) a =
      ∫ r in (0 : ℝ)..1, g r := by
  apply orbit_stationarity_of_balance g D order (MonoidHom.id (Equiv.Perm C))
    Finset.univ _ (fun sigma b => huniform (sigma b) b) a
  · intro b _
    exact ⟨Equiv.swap a b, by simp⟩
  · simpa only [hsum] using (show (0 : ℝ) < 1 by norm_num)
  · simpa only [hsum, one_mul, expectation] using
      symmetrized_partition g D order (MonoidHom.id (Equiv.Perm C)) hcont hD hsum

/-- Any nonempty finite collection of rankings gives an actual equally weighted
election in the paper's formal model. Repeated voter types can be represented
by distinct indices carrying the same ranking. -/
noncomputable def profileElection {V : Type*} [Fintype V] [Nonempty V]
    {m : ℕ} (hm : 0 < m) (orders : V → Equiv.Perm (Fin m)) : Election where
  voterCount := Fintype.card V
  candidateCount := m
  voters_pos := Fintype.card_pos
  candidates_pos := hm
  order i := orders ((Fintype.equivFin V).symm i)

/-- This construction uses the exact uniform finite average, not real voter weights. -/
theorem profileElection_average {V : Type*} [Fintype V] [Nonempty V]
    {m : ℕ} (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (g : ℝ → ℝ) (D : Lottery m) (a : Fin m) :
    expectation (profileElection hm orders).voterWeight
      (fun v => (profileElection hm orders).activation g D v a) =
        (∑ v : V, orderedActivation g D.weight (orders v) a) / Fintype.card V := by
  change (∑ i : Fin (Fintype.card V), (1 / (Fintype.card V : ℝ)) *
    orderedActivation g D.weight (orders ((Fintype.equivFin V).symm i)) a) = _
  rw [← Finset.mul_sum]
  have hsum := Equiv.sum_comp (Fintype.equivFin V).symm
    (fun v : V => orderedActivation g D.weight (orders v) a)
  rw [hsum]
  ring

/-- Stability of the concrete profile is exactly its finitely averaged inequality. -/
theorem profileElection_stable_iff {V : Type*} [Fintype V] [Nonempty V]
    {m : ℕ} (hm : 0 < m) (orders : V → Equiv.Perm (Fin m))
    (g : ℝ → ℝ) (D : Lottery m) :
    (profileElection hm orders).Stable g D ↔
      ∀ a, (∑ v : V, orderedActivation g D.weight (orders v) a) / Fintype.card V ≤
        ∫ r in (0 : ℝ)..1, g r := by
  constructor
  · intro h a
    simpa only [profileElection_average] using h a
  · intro h a
    simpa only [profileElection_average] using h a

/-- Applying every permutation in a finite group is an equally weighted finite election. -/
noncomputable def symmetrizedElection {G : Type*} [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (order : Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) : Election :=
  profileElection hm (fun sigma => order.trans (action sigma))

theorem symmetrizedElection_average {G : Type*} [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (order : Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Lottery m) (a : Fin m) :
    expectation (symmetrizedElection hm order action).voterWeight
      (fun v => (symmetrizedElection hm order action).activation g D v a) =
        symmetrizedActivation g D.weight order action a :=
  profileElection_average hm _ g D a

/-- A uniform lottery is exactly stable in the finite profile containing all
candidate permutations, for every continuous activation. -/
theorem full_symmetry_election_stable {m : ℕ} (hm : 0 < m)
    (order : Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Lottery m)
    (hg : ContinuousOn g (Icc 0 1)) (hD : ∀ a b, D.weight a = D.weight b) :
    (symmetrizedElection hm order (MonoidHom.id (Equiv.Perm (Fin m)))).Stable g D := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  intro a
  rw [symmetrizedElection_average]
  exact le_of_eq (full_symmetry_stationary g D.weight order hg D.nonneg D.total hD a)

/-- Several base voter types, each symmetrized separately; all resulting voters
have equal weight. A type can occur repeatedly in the finite index type T. -/
noncomputable def mixedSymmetrizedElection {T G : Type*}
    [Fintype T] [Nonempty T] [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (orders : T → Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) : Election :=
  profileElection hm (fun pair : T × G => (orders pair.1).trans (action pair.2))

theorem mixedSymmetrizedElection_average {T G : Type*}
    [Fintype T] [Nonempty T] [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (orders : T → Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Lottery m) (a : Fin m) :
    expectation (mixedSymmetrizedElection hm orders action).voterWeight
      (fun v => (mixedSymmetrizedElection hm orders action).activation g D v a) =
        (∑ t : T, symmetrizedActivation g D.weight (orders t) action a) / Fintype.card T := by
  calc
    _ = (∑ pair : T × G, orderedActivation g D.weight
        ((orders pair.1).trans (action pair.2)) a) / Fintype.card (T × G) :=
      profileElection_average hm _ g D a
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, symmetrizedActivation]
      rw [← Finset.sum_div, div_div, mul_comm (Fintype.card G : ℝ)]

/-- Constant-per-class lottery weights on two finite supported classes. -/
def twoClassWeight {H Z : Type*} (alpha beta : ℝ) : H ⊕ Z → ℝ :=
  Sum.elim (fun _ => alpha) (fun _ => beta)

theorem twoClassWeight_invariant {H Z : Type*} (alpha beta : ℝ)
    (sigma : Equiv.Perm H × Equiv.Perm Z) (a : H ⊕ Z) :
    twoClassWeight alpha beta (Equiv.Perm.sumCongrHom H Z sigma a) =
      twoClassWeight alpha beta a := by
  cases a <;> rfl

/-- Exact finite symmetry within the first supported class. -/
theorem twoClass_score_left {H Z : Type*} [Fintype H] [Fintype Z]
    [DecidableEq H] [DecidableEq Z] {n : ℕ}
    (g : ℝ → ℝ) (alpha beta : ℝ) (order : Fin n ≃ H ⊕ Z) (a b : H) :
    symmetrizedActivation g (twoClassWeight alpha beta) order
      (Equiv.Perm.sumCongrHom H Z) (Sum.inl a) =
    symmetrizedActivation g (twoClassWeight alpha beta) order
      (Equiv.Perm.sumCongrHom H Z) (Sum.inl b) := by
  have h := symmetrizedActivation_invariant g (twoClassWeight alpha beta) order
    (Equiv.Perm.sumCongrHom H Z) (twoClassWeight_invariant alpha beta)
    (Equiv.swap a b, 1) (Sum.inl a)
  simpa using h.symm

/-- Exact finite symmetry within the second supported class. -/
theorem twoClass_score_right {H Z : Type*} [Fintype H] [Fintype Z]
    [DecidableEq H] [DecidableEq Z] {n : ℕ}
    (g : ℝ → ℝ) (alpha beta : ℝ) (order : Fin n ≃ H ⊕ Z) (a b : Z) :
    symmetrizedActivation g (twoClassWeight alpha beta) order
      (Equiv.Perm.sumCongrHom H Z) (Sum.inr a) =
    symmetrizedActivation g (twoClassWeight alpha beta) order
      (Equiv.Perm.sumCongrHom H Z) (Sum.inr b) := by
  have h := symmetrizedActivation_invariant g (twoClassWeight alpha beta) order
    (Equiv.Perm.sumCongrHom H Z) (twoClassWeight_invariant alpha beta)
    (1, Equiv.swap a b) (Sum.inr a)
  simpa using h.symm

/-- A fixed candidate has the same activation in every relabeling. -/
theorem symmetrizedActivation_fixed {C G : Type*} [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C)
    (hD : ∀ sigma a, D (action sigma a) = D a)
    (a : C) (hfixed : ∀ sigma, action sigma a = a) :
    symmetrizedActivation g D order action a = orderedActivation g D order a := by
  have hpoint : ∀ sigma : G,
      orderedActivation g D (order.trans (action sigma)) a = orderedActivation g D order a := by
    intro sigma
    rw [orderedActivation_relabel g D order (action sigma) (hD sigma)]
    have hinv : (action sigma).symm a = a := by
      calc
        _ = (action sigma).symm (action sigma a) := congrArg (action sigma).symm (hfixed sigma).symm
        _ = a := Equiv.symm_apply_apply _ _
    rw [hinv]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Fintype.card_pos (α := G))
  simp [symmetrizedActivation, hpoint, hcard]

/-- If all supported candidates form one orbit, every supported candidate is
stationary. Unsupported candidates contribute zero to the partition identity. -/
theorem one_supported_orbit_stationary {C G : Type*}
    [Fintype C] [Fintype G] [Group G] {n : ℕ}
    (g : ℝ → ℝ) (D : C → ℝ) (order : Fin n ≃ C)
    (action : G →* Equiv.Perm C)
    (hcont : ContinuousOn g (Icc 0 1))
    (hD : ∀ a, 0 ≤ D a) (hsum : ∑ a, D a = 1)
    (hinvariant : ∀ sigma a, D (action sigma a) = D a)
    (a : C) (horbit : ∀ b, D b ≠ 0 → ∃ sigma, action sigma a = b) :
    symmetrizedActivation g D order action a = ∫ r in (0 : ℝ)..1, g r := by
  have hterm : ∀ b, D b * symmetrizedActivation g D order action b =
      D b * symmetrizedActivation g D order action a := by
    intro b
    by_cases hb : D b = 0
    · simp [hb]
    · obtain ⟨sigma, rfl⟩ := horbit b hb
      rw [symmetrizedActivation_invariant g D order action hinvariant sigma a]
  have hmean := symmetrized_partition g D order action hcont hD hsum
  unfold expectation at hmean
  simp_rw [hterm] at hmean
  simpa only [← Finset.sum_mul, hsum, one_mul] using hmean

/-- The full Election 1 stability criterion for a finite group-symmetrized
profile: one supported orbit and fixed unsupported candidates. -/
theorem one_orbit_election_stable {G : Type*} [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (order : Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Lottery m)
    (hcont : ContinuousOn g (Icc 0 1))
    (hinvariant : ∀ sigma a, D.weight (action sigma a) = D.weight a)
    (htransitive : ∀ a b, D.weight a ≠ 0 → D.weight b ≠ 0 →
      ∃ sigma, action sigma a = b)
    (hfixed : ∀ a, D.weight a = 0 → ∀ sigma, action sigma a = a)
    (hunsupported : ∀ a, D.weight a = 0 →
      orderedActivation g D.weight order a ≤ ∫ r in (0 : ℝ)..1, g r) :
    (symmetrizedElection hm order action).Stable g D := by
  intro a
  rw [symmetrizedElection_average]
  by_cases ha : D.weight a = 0
  · rw [symmetrizedActivation_fixed g D.weight order action hinvariant a (hfixed a ha)]
    exact hunsupported a ha
  · exact le_of_eq (one_supported_orbit_stationary g D.weight order action hcont
      D.nonneg D.total hinvariant a (fun b hb => htransitive a b ha hb))

/-- Finite mixtures preserve supported stationarity, while the unsupported
candidate test is exactly the finite average of its original activation. -/
theorem one_orbit_mixed_election_stable {T G : Type*}
    [Fintype T] [Nonempty T] [Fintype G] [Group G]
    {m : ℕ} (hm : 0 < m) (orders : T → Equiv.Perm (Fin m))
    (action : G →* Equiv.Perm (Fin m)) (g : ℝ → ℝ) (D : Lottery m)
    (hcont : ContinuousOn g (Icc 0 1))
    (hinvariant : ∀ sigma a, D.weight (action sigma a) = D.weight a)
    (htransitive : ∀ a b, D.weight a ≠ 0 → D.weight b ≠ 0 →
      ∃ sigma, action sigma a = b)
    (hfixed : ∀ a, D.weight a = 0 → ∀ sigma, action sigma a = a)
    (hunsupported : ∀ a, D.weight a = 0 →
      (∑ t : T, orderedActivation g D.weight (orders t) a) / Fintype.card T ≤
        ∫ r in (0 : ℝ)..1, g r) :
    (mixedSymmetrizedElection hm orders action).Stable g D := by
  intro a
  rw [mixedSymmetrizedElection_average]
  by_cases ha : D.weight a = 0
  · simp_rw [symmetrizedActivation_fixed g D.weight _ action hinvariant a (hfixed a ha)]
    exact hunsupported a ha
  · have hpoint : ∀ t : T, symmetrizedActivation g D.weight (orders t) action a =
        ∫ r in (0 : ℝ)..1, g r := by
      intro t
      exact one_supported_orbit_stationary g D.weight (orders t) action hcont
        D.nonneg D.total hinvariant a (fun b hb => htransitive a b ha hb)
    have hcard : (Fintype.card T : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Fintype.card_pos (α := T))
    simp [hpoint, hcard]

/-- Election 1 at rank 1 needs only one voter and two candidates: the
unsupported reference is ranked above the candidate receiving all lottery mass. -/
abbrev topReferenceElection : Election where
  voterCount := 1
  candidateCount := 2
  voters_pos := by decide
  candidates_pos := by decide
  order _ := Equiv.refl _

abbrev topReferenceLottery : Lottery 2 where
  weight := ![1, 0]
  nonneg := by intro a; fin_cases a <;> norm_num
  total := by norm_num [Fin.sum_univ_two]

def topReferenceHeight : Fin 2 → ℝ := ![1, 0]

theorem topReferenceHeight_nonneg (a : Fin 2) : 0 ≤ topReferenceHeight a := by
  fin_cases a <;> norm_num [topReferenceHeight]

theorem topReference_supported_activation (g : ℝ → ℝ) (v : topReferenceElection.Voter) :
    topReferenceElection.activation g topReferenceLottery v 0 = ∫ r in (0 : ℝ)..1, g r := by
  change rankActivation g (fun i : Fin 2 => ![1, 0] i) (0 : Fin 2) = _
  simp [rankActivation, rankCut_zero]

theorem topReference_unsupported_activation (g : ℝ → ℝ) (v : topReferenceElection.Voter) :
    topReferenceElection.activation g topReferenceLottery v 1 = g 1 := by
  change rankActivation g (fun i : Fin 2 => ![1, 0] i) (1 : Fin 2) = _
  simp [rankActivation, rankCut]

/-- If g(1) is no larger than its mean, this concrete lottery is exactly stable. -/
theorem topReference_stable (g : ℝ → ℝ)
    (hendpoint : g 1 ≤ ∫ r in (0 : ℝ)..1, g r) :
    topReferenceElection.Stable g topReferenceLottery := by
  have h0 : expectation topReferenceElection.voterWeight
      (fun v => topReferenceElection.activation g topReferenceLottery v 0) =
        ∫ r in (0 : ℝ)..1, g r := by
    calc
      _ = expectation topReferenceElection.voterWeight
          (fun _ => ∫ r in (0 : ℝ)..1, g r) :=
        congrArg (expectation topReferenceElection.voterWeight)
          (funext (topReference_supported_activation g))
      _ = _ := expectation_const topReferenceElection.voterWeight_total _
  have h1 : expectation topReferenceElection.voterWeight
      (fun v => topReferenceElection.activation g topReferenceLottery v 1) = g 1 := by
    calc
      _ = expectation topReferenceElection.voterWeight (fun _ => g 1) :=
        congrArg (expectation topReferenceElection.voterWeight)
          (funext (topReference_unsupported_activation g))
      _ = _ := expectation_const topReferenceElection.voterWeight_total _
  intro a
  change Fin 2 at a
  fin_cases a
  · exact le_of_eq h0
  · exact le_trans (le_of_eq h1) hendpoint

theorem topReference_runningMin (v : topReferenceElection.Voter) (b : Fin 2) :
    runningMin (topReferenceElection.ordinalRank v) topReferenceHeight b = topReferenceHeight b := by
  apply le_antisymm (runningMin_le_self _ _ b)
  apply Finset.le_inf'
  intro c _
  change topReferenceHeight b ≤ if c.val ≤ b.val then topReferenceHeight c else topReferenceHeight b
  fin_cases b <;> fin_cases c <;> norm_num [topReferenceHeight]

theorem topReference_maximumGap (v : topReferenceElection.Voter) :
    maximumGap (topReferenceElection.ordinalRank v) topReferenceHeight = 0 := by
  unfold maximumGap
  apply Finset.sup'_eq_of_forall
  intro b _
  rw [topReference_runningMin]
  ring

theorem topReference_expected_runningMin :
    expectation topReferenceElection.voterWeight (fun v =>
      expectation topReferenceLottery.weight
        (runningMin (topReferenceElection.ordinalRank v) topReferenceHeight)) = 1 := by
  have hpoint : ∀ v : topReferenceElection.Voter,
      expectation topReferenceLottery.weight
        (runningMin (topReferenceElection.ordinalRank v) topReferenceHeight) = 1 := by
    intro v
    have hfun : runningMin (topReferenceElection.ordinalRank v) topReferenceHeight =
        topReferenceHeight := funext (topReference_runningMin v)
    rw [hfun]
    norm_num [expectation, topReferenceLottery, topReferenceHeight, Fin.sum_univ_two]
  simp_rw [hpoint]
  exact expectation_const topReferenceElection.voterWeight_total 1

theorem topReference_expected_gap :
    expectation topReferenceElection.voterWeight
      (fun v => maximumGap (topReferenceElection.ordinalRank v) topReferenceHeight) = 0 := by
  simp_rw [topReference_maximumGap]
  exact expectation_const topReferenceElection.voterWeight_total 0

/-- The rank-one election yields an actual finite metric witness above every
finite distortion target of the form 1+2lam. -/
theorem topReference_witnessAbove (g : ℝ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hendpoint : g 1 ≤ ∫ r in (0 : ℝ)..1, g r) : WitnessAbove g (1 + 2 * lam) := by
  have hviolation : lam * expectation topReferenceElection.voterWeight
      (fun v => maximumGap (topReferenceElection.ordinalRank v) topReferenceHeight) <
      expectation topReferenceElection.voterWeight (fun v =>
        expectation topReferenceLottery.weight
          (runningMin (topReferenceElection.ordinalRank v) topReferenceHeight)) := by
    rw [topReference_expected_runningMin, topReference_expected_gap]
    norm_num
  obtain ⟨metric, hconsistent, _hminimal, hpositive, hratio⟩ :=
    exists_metric_of_strict_runningMin_violation
      topReferenceElection.ordinalRank topReferenceHeight topReferenceElection.voterWeight
      topReferenceLottery.weight lam topReferenceHeight_nonneg
      topReferenceElection.voterWeight_nonneg topReferenceElection.voterWeight_total
      topReferenceLottery.total hlam (1 : Fin 2) (by norm_num [topReferenceHeight]) hviolation
  refine ⟨topReferenceElection, topReferenceLottery, topReference_stable g hendpoint,
    metric.toPseudoMetricSpace, hconsistent, 1, hpositive, ?_⟩
  rw [Election.lotteryCost_eq_voter_average]
  exact (lt_div_iff₀ hpositive).mp hratio

/-- The first necessary condition in Lemma 3.1, now from a fully finite witness. -/
theorem endpoint_above_mean_of_universalBound (g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hbound : UniversalBound g (1 + 2 * lam)) :
    (∫ r in (0 : ℝ)..1, g r) < g 1 := by
  by_contra h
  exact witnessAbove_not_universalBound g _
    (topReference_witnessAbove g lam hlam (le_of_not_gt h)) hbound

end OptimalG
