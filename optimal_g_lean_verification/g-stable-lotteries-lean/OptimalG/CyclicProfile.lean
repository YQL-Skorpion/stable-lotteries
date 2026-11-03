import OptimalG.CyclicJacobian

/-!
# Actual consecutive-triple ranking profiles

The six orders are concrete candidate permutations. They realize the cyclic
and reversed profiles used in the auxiliary Jacobian construction.
-/

namespace OptimalG
open scoped BigOperators

noncomputable def cyclicOrders {C : Type*} [DecidableEq C] (a b c : C) :
    Fin 6 → Equiv.Perm C :=
  ![Equiv.refl C, (Equiv.swap a b).trans (Equiv.swap a c),
    (Equiv.swap a c).trans (Equiv.swap a b), Equiv.swap a c, Equiv.swap b c, Equiv.swap a b]

theorem cyclicOrders_outside {C : Type*} [DecidableEq C] (a b c x : C)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (i : Fin 6) :
    cyclicOrders a b c i x = x := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, hxa, hxb, hxc]

theorem cyclicOrders_inverse_first {C : Type*} [DecidableEq C] (a b c : C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 6) :
    (cyclicOrders a b c i).symm a = ![a, c, b, c, a, b] i := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem cyclicOrders_first {C : Type*} [DecidableEq C] (a b c : C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 6) :
    cyclicOrders a b c i a = ![a, b, c, c, a, b] i := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem cyclicOrders_second {C : Type*} [DecidableEq C] (a b c : C)
    (hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c) (i : Fin 6) :
    cyclicOrders a b c i b = ![b, c, a, b, c, a] i := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, Ne.symm hab, hbc]

theorem cyclicOrders_inverse_second {C : Type*} [DecidableEq C] (a b c : C)
    (hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c) (i : Fin 6) :
    (cyclicOrders a b c i).symm b = ![b, a, c, b, c, a] i := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, Ne.symm hab, hbc]

theorem cyclicOrders_inverse_third {C : Type*} [DecidableEq C] (a b c : C)
    (_hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 6) :
    (cyclicOrders a b c i).symm c = ![c, b, a, a, b, c] i := by
  fin_cases i <;> simp [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, Ne.symm hac, Ne.symm hbc]

/-- Everything below the consecutive triple is fixed by all six permutations. -/
theorem cyclicOrders_prefix {m : ℕ} (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (h : Fin m → ℝ) (i : Fin 6) :
    rankCut (fun j => h (cyclicOrders a b c i j)) a.val = rankCut h a.val := by
  unfold rankCut
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < a.val
  · have hja : j ≠ a := by intro heq; subst j; omega
    have hjb : j ≠ b := by intro heq; subst j; omega
    have hjc : j ≠ c := by intro heq; subst j; omega
    simp only [if_pos hj, cyclicOrders_outside a b c j hja hjb hjc]
  · simp only [if_neg hj]

/-- The actual rank-prefix variations for the distinguished member of a
consecutive triple, in the six explicit permutations. -/
theorem cyclicOrders_prefix_variation {m : ℕ} (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (h : Fin m → ℝ) (i : Fin 6) :
    rankPrefixLinear (cyclicOrders a b c i) a h =
      ![rankCut h a.val, rankCut h a.val + h b + h c, rankCut h a.val + h c,
        rankCut h a.val + h c + h b, rankCut h a.val, rankCut h a.val + h b] i := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac' : a ≠ c := by intro h; subst c; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hprefix := cyclicOrders_prefix a b c hab hbc h i
  have hB : rankCut (fun j => h (cyclicOrders a b c i j)) b.val =
      rankCut h a.val + h (cyclicOrders a b c i a) := by
    rw [← hab, rankCut_succ, hprefix]
  have hC : rankCut (fun j => h (cyclicOrders a b c i j)) c.val =
      rankCut h a.val + h (cyclicOrders a b c i a) + h (cyclicOrders a b c i b) := by
    rw [← hbc, rankCut_succ, hB]
  rw [rankPrefixLinear_apply, cyclicOrders_inverse_first a b c hab' hac' hbc']
  fin_cases i <;> simp_all [cyclicOrders, Equiv.swap_apply_of_ne_of_ne,
    Ne.symm hab', Ne.symm hac', Ne.symm hbc']

theorem cyclicOrders_prefix_variation_second {m : ℕ} (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (h : Fin m → ℝ) (i : Fin 6) :
    rankPrefixLinear (cyclicOrders a b c i) b h =
      ![rankCut h a.val + h a, rankCut h a.val, rankCut h a.val + h c + h a, rankCut h a.val + h c, rankCut h a.val + h a + h c, rankCut h a.val] i := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac' : a ≠ c := by intro h; subst c; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hprefix := cyclicOrders_prefix a b c hab hbc h i
  have hB : rankCut (fun j => h (cyclicOrders a b c i j)) b.val =
      rankCut h a.val + h (cyclicOrders a b c i a) := by
    rw [← hab, rankCut_succ, hprefix]
  have hC : rankCut (fun j => h (cyclicOrders a b c i j)) c.val =
      rankCut h a.val + h (cyclicOrders a b c i a) + h (cyclicOrders a b c i b) := by
    rw [← hbc, rankCut_succ, hB]
  rw [rankPrefixLinear_apply, cyclicOrders_inverse_second a b c hab' hac' hbc']
  fin_cases i <;> simp_all [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, Ne.symm hab', Ne.symm hac', Ne.symm hbc']

theorem cyclicOrders_prefix_variation_third {m : ℕ} (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (h : Fin m → ℝ) (i : Fin 6) :
    rankPrefixLinear (cyclicOrders a b c i) c h =
      ![rankCut h a.val + h a + h b, rankCut h a.val + h b, rankCut h a.val, rankCut h a.val, rankCut h a.val + h a, rankCut h a.val + h b + h a] i := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac' : a ≠ c := by intro h; subst c; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  have hprefix := cyclicOrders_prefix a b c hab hbc h i
  have hB : rankCut (fun j => h (cyclicOrders a b c i j)) b.val =
      rankCut h a.val + h (cyclicOrders a b c i a) := by
    rw [← hab, rankCut_succ, hprefix]
  have hC : rankCut (fun j => h (cyclicOrders a b c i j)) c.val =
      rankCut h a.val + h (cyclicOrders a b c i a) + h (cyclicOrders a b c i b) := by
    rw [← hbc, rankCut_succ, hB]
  rw [rankPrefixLinear_apply, cyclicOrders_inverse_third a b c hab' hac' hbc']
  fin_cases i <;> simp_all [cyclicOrders, Equiv.swap_apply_of_ne_of_ne, Ne.symm hab', Ne.symm hac', Ne.symm hbc']

/-- Constant candidate masses give consecutive rank intervals of that mass. -/
theorem cyclicOrders_prefix_mass {m : ℕ} (a b c : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val) (u : ℝ) (i : Fin 6) :
    rankPrefixLinear (cyclicOrders a b c i) a (fun _ => u) =
      ![rankCut (fun _ : Fin m => u) a.val,
        rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val + u,
        rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val,
        rankCut (fun _ : Fin m => u) a.val + u] i := by
  rw [cyclicOrders_prefix_variation a b c hab hbc]
  fin_cases i <;> simp <;> ring

/-- The printed cyclic-triple Jacobian entry, now for actual permutations and
actual activation derivatives on a uniform positive-mass lottery. -/
theorem cyclicOrders_actual_derivative {m : ℕ} (g : ℝ → ℝ)
    (a b c : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (u : ℝ) (hu : u ≠ 0) (h : Fin m → ℝ) :
    (scoreDerivative g (cyclicOrders a b c 0) a (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 1) a (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 2) a (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 3) a (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 4) a (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 5) a (fun _ => u) h) / 3 =
        ((g (rankCut (fun _ : Fin m => u) a.val + 2 * u) -
          g (rankCut (fun _ : Fin m => u) a.val + u)) / (3 * u)) * (h c - h b) := by
  exact cyclic_actual_score_derivative g (cyclicOrders a b c) a (fun _ => u) h _ u _ (h b) (h c)
    hu rfl (cyclicOrders_prefix_mass a b c hab hbc u) (cyclicOrders_prefix_variation a b c hab hbc h)

/-- The corresponding cyclic Jacobian entry for the second candidate. -/
theorem cyclicOrders_actual_derivative_second {m : ℕ} (g : ℝ → ℝ)
    (a b c : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (u : ℝ) (hu : u ≠ 0) (h : Fin m → ℝ) :
    (scoreDerivative g (cyclicOrders a b c 0) b (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 1) b (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 2) b (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 3) b (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 4) b (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 5) b (fun _ => u) h) / 3 =
        ((g (rankCut (fun _ : Fin m => u) a.val + 2 * u) -
          g (rankCut (fun _ : Fin m => u) a.val + u)) / (3 * u)) * (h a - h c) := by
  let orders : Fin 6 → Equiv.Perm (Fin m) := fun i => cyclicOrders a b c (![1, 2, 0, 4, 5, 3] i)
  have hvariation (i : Fin 6) : rankPrefixLinear (orders i) b h =
      ![rankCut h a.val, rankCut h a.val + h c + h a, rankCut h a.val + h a,
        rankCut h a.val + h a + h c, rankCut h a.val, rankCut h a.val + h c] i := by
    dsimp only [orders]
    rw [cyclicOrders_prefix_variation_second a b c hab hbc]
    fin_cases i <;> rfl
  have hmass (i : Fin 6) : rankPrefixLinear (orders i) b (fun _ => u) =
      ![rankCut (fun _ : Fin m => u) a.val, rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val + u, rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val, rankCut (fun _ : Fin m => u) a.val + u] i := by
    dsimp only [orders]
    rw [cyclicOrders_prefix_variation_second a b c hab hbc]
    fin_cases i
    · rfl
    · change rankCut (fun _ : Fin m => u) a.val + u + u = rankCut (fun _ : Fin m => u) a.val + 2 * u
      ring
    · rfl
    · change rankCut (fun _ : Fin m => u) a.val + u + u = rankCut (fun _ : Fin m => u) a.val + 2 * u
      ring
    · rfl
    · rfl
  have hresult := cyclic_actual_score_derivative g orders b (fun _ => u) h _ u _ (h c) (h a)
    hu rfl hmass hvariation
  convert hresult using 1
  simp [orders]
  ring

/-- The corresponding cyclic Jacobian entry for the third candidate. -/
theorem cyclicOrders_actual_derivative_third {m : ℕ} (g : ℝ → ℝ)
    (a b c : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (u : ℝ) (hu : u ≠ 0) (h : Fin m → ℝ) :
    (scoreDerivative g (cyclicOrders a b c 0) c (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 1) c (fun _ => u) h +
      scoreDerivative g (cyclicOrders a b c 2) c (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 3) c (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 4) c (fun _ => u) h -
      scoreDerivative g (cyclicOrders a b c 5) c (fun _ => u) h) / 3 =
        ((g (rankCut (fun _ : Fin m => u) a.val + 2 * u) -
          g (rankCut (fun _ : Fin m => u) a.val + u)) / (3 * u)) * (h b - h a) := by
  let orders : Fin 6 → Equiv.Perm (Fin m) := fun i => cyclicOrders a b c (![2, 0, 1, 5, 3, 4] i)
  have hvariation (i : Fin 6) : rankPrefixLinear (orders i) c h =
      ![rankCut h a.val, rankCut h a.val + h a + h b, rankCut h a.val + h b,
        rankCut h a.val + h b + h a, rankCut h a.val, rankCut h a.val + h a] i := by
    dsimp only [orders]
    rw [cyclicOrders_prefix_variation_third a b c hab hbc]
    fin_cases i <;> rfl
  have hmass (i : Fin 6) : rankPrefixLinear (orders i) c (fun _ => u) =
      ![rankCut (fun _ : Fin m => u) a.val, rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val + u, rankCut (fun _ : Fin m => u) a.val + 2 * u,
        rankCut (fun _ : Fin m => u) a.val, rankCut (fun _ : Fin m => u) a.val + u] i := by
    dsimp only [orders]
    rw [cyclicOrders_prefix_variation_third a b c hab hbc]
    fin_cases i
    · rfl
    · change rankCut (fun _ : Fin m => u) a.val + u + u = rankCut (fun _ : Fin m => u) a.val + 2 * u
      ring
    · rfl
    · change rankCut (fun _ : Fin m => u) a.val + u + u = rankCut (fun _ : Fin m => u) a.val + 2 * u
      ring
    · rfl
    · rfl
  have hresult := cyclic_actual_score_derivative g orders c (fun _ => u) h _ u _ (h a) (h b)
    hu rfl hmass hvariation
  convert hresult using 1
  simp [orders]
  ring

theorem rankCut_swap_same_side {m : ℕ} (a b : Fin m) (k : ℕ)
    (hside : a.val < k ↔ b.val < k) (h : Fin m → ℝ) :
    rankCut (fun j => h (Equiv.swap a b j)) k = rankCut h k := by
  have hpred (j : Fin m) : j.val < k ↔ (Equiv.swap a b j).val < k := by
    by_cases hja : j = a
    · subst j; simpa using hside
    by_cases hjb : j = b
    · subst j; simpa using hside.symm
    rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
  unfold rankCut
  calc
    _ = ∑ j, if (Equiv.swap a b j).val < k then h (Equiv.swap a b j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [hpred j]
    _ = _ := Equiv.sum_comp (Equiv.swap a b) (fun j => if j.val < k then h j else 0)

theorem cyclicOrders_cutoff_same_side {m : ℕ} (a b c : Fin m) (k : ℕ)
    (hab : a.val < k ↔ b.val < k) (hac : a.val < k ↔ c.val < k)
    (h : Fin m → ℝ) (i : Fin 6) :
    rankCut (fun j => h (cyclicOrders a b c i j)) k = rankCut h k := by
  have hbc := hab.symm.trans hac
  fin_cases i
  · rfl
  · change rankCut (fun j => (fun x => h (Equiv.swap a c x)) (Equiv.swap a b j)) k = _
    rw [rankCut_swap_same_side a b k hab (fun x => h (Equiv.swap a c x)), rankCut_swap_same_side a c k hac]
  · change rankCut (fun j => (fun x => h (Equiv.swap a b x)) (Equiv.swap a c j)) k = _
    rw [rankCut_swap_same_side a c k hac (fun x => h (Equiv.swap a b x)), rankCut_swap_same_side a b k hab]
  · exact rankCut_swap_same_side a c k hac h
  · exact rankCut_swap_same_side b c k hbc h
  · exact rankCut_swap_same_side a b k hab h

/-- Candidates outside the triple see the same lower prefix in all six orders. -/
theorem cyclicOrders_unaffected_prefix {m : ℕ} (a b c x : Fin m)
    (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (h : Fin m → ℝ) (i : Fin 6) :
    rankPrefixLinear (cyclicOrders a b c i) x h = rankCut h x.val := by
  have hxa' : x.val ≠ a.val := fun heq => hxa (Fin.ext heq)
  have hxb' : x.val ≠ b.val := fun heq => hxb (Fin.ext heq)
  have hxc' : x.val ≠ c.val := fun heq => hxc (Fin.ext heq)
  have hfix : (cyclicOrders a b c i).symm x = x := by
    apply (cyclicOrders a b c i).injective
    rw [Equiv.apply_symm_apply, cyclicOrders_outside a b c x hxa hxb hxc]
  rw [rankPrefixLinear_apply, hfix]
  exact cyclicOrders_cutoff_same_side a b c x.val (by omega) (by omega) h i

/-- Every entry outside the three affected rows of the actual derivative is zero. -/
theorem cyclicOrders_actual_derivative_outside {m : ℕ} (g : ℝ → ℝ)
    (a b c x : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (D h : Fin m → ℝ) (hDx : D x ≠ 0) :
    (scoreDerivative g (cyclicOrders a b c 0) x D h +
      scoreDerivative g (cyclicOrders a b c 1) x D h +
      scoreDerivative g (cyclicOrders a b c 2) x D h -
      scoreDerivative g (cyclicOrders a b c 3) x D h -
      scoreDerivative g (cyclicOrders a b c 4) x D h -
      scoreDerivative g (cyclicOrders a b c 5) x D h) / 3 = 0 := by
  apply cyclic_unaffected_score_derivative g (cyclicOrders a b c) x D h hDx
  · intro i
    rw [cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc,
      cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc]
  · intro i
    rw [cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc,
      cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc]

noncomputable def signedSix (f : Fin 6 → ℝ) : ℝ :=
  (f 0 + f 1 + f 2 - f 3 - f 4 - f 5) / 3

theorem orderedActivation_eq_of_rankPrefix {m : ℕ} (g : ℝ → ℝ)
    (D : Fin m → ℝ) (p q : Equiv.Perm (Fin m)) (x : Fin m)
    (hprefix : rankPrefixLinear p x D = rankPrefixLinear q x D) :
    orderedActivation g D p x = orderedActivation g D q x := by
  unfold orderedActivation rankActivation
  simp only [Equiv.apply_symm_apply, ← rankPrefixLinear_apply, hprefix]

/-- Every candidate's activation is unchanged by adding the signed cyclic
profile at a uniform lottery. This is exact, not a derivative assertion. -/
theorem cyclicOrders_signed_activation_zero {m : ℕ} (g : ℝ → ℝ)
    (a b c : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (u : ℝ) (x : Fin m) :
    signedSix (fun i => orderedActivation g (fun _ => u) (cyclicOrders a b c i) x) = 0 := by
  have heq (i j : Fin 6) (hp : rankPrefixLinear (cyclicOrders a b c i) x (fun _ => u) =
      rankPrefixLinear (cyclicOrders a b c j) x (fun _ => u)) :=
    orderedActivation_eq_of_rankPrefix g (fun _ => u) (cyclicOrders a b c i) (cyclicOrders a b c j) x hp
  unfold signedSix
  by_cases hxa : x = a
  · subst x
    have h04 := heq 0 4 (by rw [cyclicOrders_prefix_variation a b c hab hbc,
      cyclicOrders_prefix_variation a b c hab hbc]; rfl)
    have h13 := heq 1 3 (by rw [cyclicOrders_prefix_variation a b c hab hbc,
      cyclicOrders_prefix_variation a b c hab hbc]; rfl)
    have h25 := heq 2 5 (by rw [cyclicOrders_prefix_variation a b c hab hbc,
      cyclicOrders_prefix_variation a b c hab hbc]; rfl)
    simp only [h04, h13, h25]
    ring
  by_cases hxb : x = b
  · subst x
    have h03 := heq 0 3 (by rw [cyclicOrders_prefix_variation_second a b c hab hbc,
      cyclicOrders_prefix_variation_second a b c hab hbc]; rfl)
    have h15 := heq 1 5 (by rw [cyclicOrders_prefix_variation_second a b c hab hbc,
      cyclicOrders_prefix_variation_second a b c hab hbc]; rfl)
    have h24 := heq 2 4 (by rw [cyclicOrders_prefix_variation_second a b c hab hbc,
      cyclicOrders_prefix_variation_second a b c hab hbc]; rfl)
    simp only [h03, h15, h24]
    ring
  by_cases hxc : x = c
  · subst x
    have h05 := heq 0 5 (by rw [cyclicOrders_prefix_variation_third a b c hab hbc,
      cyclicOrders_prefix_variation_third a b c hab hbc]; rfl)
    have h14 := heq 1 4 (by rw [cyclicOrders_prefix_variation_third a b c hab hbc,
      cyclicOrders_prefix_variation_third a b c hab hbc]; rfl)
    have h23 := heq 2 3 (by rw [cyclicOrders_prefix_variation_third a b c hab hbc,
      cyclicOrders_prefix_variation_third a b c hab hbc]; rfl)
    simp only [h05, h14, h23]
    ring
  · have hsame (i : Fin 6) := heq i 0 (by
      rw [cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc,
        cyclicOrders_unaffected_prefix a b c x hab hbc hxa hxb hxc])
    simp only [hsame]
    ring

end OptimalG
