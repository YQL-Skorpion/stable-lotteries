import OptimalG.CyclicProfile
import OptimalG.ScoreRelabel
import Mathlib.Logic.Equiv.Fintype

/-!
# Cyclic perturbations on arbitrary candidate triples

A finite permutation sends the consecutive rank positions to any three distinct
candidate labels. The resulting six genuine rankings preserve every candidate's
activation at a uniform lottery and have exactly the claimed skew derivative.
-/

namespace OptimalG

/-- Three distinct labels can be sent to any other three distinct labels. -/
theorem exists_relabel_triple {C : Type*} (a b c x y z : C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ sigma : Equiv.Perm C, sigma a = x ∧ sigma b = y ∧ sigma c = z := by
  have hf : Function.Injective (![a, b, c] : Fin 3 → C) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hg : Function.Injective (![x, y, z] : Fin 3 → C) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨sigma, hsigma⟩ := Equiv.Perm.exists_extending_pair ![a, b, c] ![x, y, z] hf hg
  exact ⟨sigma, hsigma 0, hsigma 1, hsigma 2⟩

noncomputable def cyclicStrength {m : ℕ} (g : ℝ → ℝ) (a : Fin m) (u : ℝ) : ℝ :=
  (g (rankCut (fun _ : Fin m => u) a.val + 2 * u) -
    g (rankCut (fun _ : Fin m => u) a.val + u)) / (3 * u)

/-- A completely finite realization of each local auxiliary skew matrix. -/
theorem exists_cyclic_profile {m : ℕ} (g : ℝ → ℝ)
    (a b c : Fin m) (hab : a.val + 1 = b.val) (hbc : b.val + 1 = c.val)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (u : ℝ) (hu : u ≠ 0) :
    ∃ orders : Fin 6 → Equiv.Perm (Fin m),
      (∀ q, signedSix (fun i => orderedActivation g (fun _ => u) (orders i) q) = 0) ∧
      (∀ h : Fin m → ℝ,
        signedSix (fun i => scoreDerivative g (orders i) x (fun _ => u) h) =
          cyclicStrength g a u * (h z - h y)) ∧
      (∀ h : Fin m → ℝ,
        signedSix (fun i => scoreDerivative g (orders i) y (fun _ => u) h) =
          cyclicStrength g a u * (h x - h z)) ∧
      (∀ h : Fin m → ℝ,
        signedSix (fun i => scoreDerivative g (orders i) z (fun _ => u) h) =
          cyclicStrength g a u * (h y - h x)) ∧
      (∀ q, q ≠ x → q ≠ y → q ≠ z → ∀ h : Fin m → ℝ,
        signedSix (fun i => scoreDerivative g (orders i) q (fun _ => u) h) = 0) := by
  have hab' : a ≠ b := by intro h; subst b; omega
  have hac' : a ≠ c := by intro h; subst c; omega
  have hbc' : b ≠ c := by intro h; subst c; omega
  obtain ⟨sigma, ha, hb, hc⟩ := exists_relabel_triple a b c x y z hab' hac' hbc' hxy hxz hyz
  let orders := fun i => (cyclicOrders a b c i).trans sigma
  have hact (q : Fin m) (i : Fin 6) :
      orderedActivation g (fun _ => u) (orders i) q =
        orderedActivation g (fun _ => u) (cyclicOrders a b c i) (sigma.symm q) := by
    simpa only [Equiv.apply_symm_apply] using
      orderedActivation_relabel_weights g (cyclicOrders a b c i) sigma (sigma.symm q) (fun _ => u)
  have hderiv (q : Fin m) (h : Fin m → ℝ) (i : Fin 6) :
      scoreDerivative g (orders i) q (fun _ => u) h =
        scoreDerivative g (cyclicOrders a b c i) (sigma.symm q) (fun _ => u) (fun r => h (sigma r)) := by
    simpa only [Equiv.apply_symm_apply] using
      scoreDerivative_relabel g (cyclicOrders a b c i) sigma (sigma.symm q) (fun _ => u) h hu
  have hsx : sigma.symm x = a := by rw [← ha, Equiv.symm_apply_apply]
  have hsy : sigma.symm y = b := by rw [← hb, Equiv.symm_apply_apply]
  have hsz : sigma.symm z = c := by rw [← hc, Equiv.symm_apply_apply]
  refine ⟨orders, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    simp only [hact]
    exact cyclicOrders_signed_activation_zero g a b c hab hbc u (sigma.symm q)
  · intro h
    unfold signedSix
    simp only [hderiv, hsx]
    simpa only [ha, hb, hc, cyclicStrength] using
      cyclicOrders_actual_derivative g a b c hab hbc u hu (fun r => h (sigma r))
  · intro h
    unfold signedSix
    simp only [hderiv, hsy]
    simpa only [ha, hb, hc, cyclicStrength] using
      cyclicOrders_actual_derivative_second g a b c hab hbc u hu (fun r => h (sigma r))
  · intro h
    unfold signedSix
    simp only [hderiv, hsz]
    simpa only [ha, hb, hc, cyclicStrength] using
      cyclicOrders_actual_derivative_third g a b c hab hbc u hu (fun r => h (sigma r))
  · intro q hqx hqy hqz h
    unfold signedSix
    simp only [hderiv]
    apply cyclicOrders_actual_derivative_outside g a b c (sigma.symm q) hab hbc
    · intro heq
      exact hqx (by rw [← ha, ← heq, Equiv.apply_symm_apply])
    · intro heq
      exact hqy (by rw [← hb, ← heq, Equiv.apply_symm_apply])
    · intro heq
      exact hqz (by rw [← hc, ← heq, Equiv.apply_symm_apply])
    · exact hu

end OptimalG
