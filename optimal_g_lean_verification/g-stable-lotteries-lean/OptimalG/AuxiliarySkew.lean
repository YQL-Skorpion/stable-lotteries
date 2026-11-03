import OptimalG.RationalImplicit

/-!
# The odd-support skew perturbation in the equal-voter argument

The support consists of one distinguished candidate and n disjoint pairs.
This file verifies the skew action, its constant kernel, and injectivity of
`a I + t B` on the zero-sum subspace. Connecting this action to derivatives of
signed ranking profiles is done separately.
-/

namespace OptimalG
open scoped BigOperators

abbrev PairedSupport (n : ℕ) := Option (Fin n ⊕ Fin n)

noncomputable def pairedSkew (n : ℕ) (d : ℝ) (h : PairedSupport n → ℝ) :
    PairedSupport n → ℝ
  | none => d * ∑ i, (h (some (Sum.inr i)) - h (some (Sum.inl i)))
  | some (Sum.inl i) => d * (h none - h (some (Sum.inr i)))
  | some (Sum.inr i) => d * (h (some (Sum.inl i)) - h none)

theorem pairedSupport_sum (n : ℕ) (h : PairedSupport n → ℝ) :
    ∑ a, h a = h none + ∑ i, (h (some (Sum.inl i)) + h (some (Sum.inr i))) := by
  simp only [PairedSupport, Fintype.sum_option, Fintype.sum_sum_type, Finset.sum_add_distrib]

theorem pairedSkew_sum (n : ℕ) (d : ℝ) (h : PairedSupport n → ℝ) :
    ∑ a, pairedSkew n d h a = 0 := by
  rw [pairedSupport_sum]
  simp only [pairedSkew]
  have hs : ∑ i, (d * (h none - h (some (Sum.inr i))) + d * (h (some (Sum.inl i)) - h none)) =
      -(d * ∑ i, (h (some (Sum.inr i)) - h (some (Sum.inl i)))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The elementary inner-product calculation behind skew symmetry. -/
theorem pairedSkew_dot_self (n : ℕ) (d : ℝ) (h : PairedSupport n → ℝ) :
    ∑ a, h a * pairedSkew n d h a = 0 := by
  rw [pairedSupport_sum]
  simp only [pairedSkew]
  rw [← mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  ring

/-- Nonzero cyclic strength makes the kernel exactly the constant vectors. -/
theorem pairedSkew_kernel_constant (n : ℕ) (d : ℝ) (hd : d ≠ 0)
    (h : PairedSupport n → ℝ) (hzero : ∀ a, pairedSkew n d h a = 0) :
    ∀ a, h a = h none := by
  intro a
  rcases a with _ | (i | i)
  · rfl
  · have hi := hzero (some (Sum.inr i))
    simp only [pairedSkew, mul_eq_zero, hd, false_or, sub_eq_zero] at hi
    exact hi
  · have hi := hzero (some (Sum.inl i))
    simp only [pairedSkew, mul_eq_zero, hd, false_or, sub_eq_zero] at hi
    exact hi.symm

/-- A constant zero-sum vector on this nonempty finite support is zero. -/
theorem pairedSupport_constant_zero (n : ℕ) (h : PairedSupport n → ℝ)
    (hsum : ∑ a, h a = 0) (hconstant : ∀ a, h a = h none) : h = 0 := by
  have hn : (Fintype.card (PairedSupport n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hz : h none = 0 := by
    simpa only [hconstant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_eq_zero, hn, false_or] using hsum
  funext a
  exact (hconstant a).trans hz

/-- The real skew perturbation has no zero-sum kernel after adding any scalar
multiple of the identity, provided the skew coefficient is nonzero. -/
theorem pairedSkew_scalar_injective_on_tangent (n : ℕ) (d a t : ℝ)
    (hd : d ≠ 0) (ht : t ≠ 0) (h : PairedSupport n → ℝ)
    (hsum : ∑ c, h c = 0)
    (heq : ∀ c, a * h c + t * pairedSkew n d h c = 0) : h = 0 := by
  by_cases ha : a = 0
  · have hzero : ∀ c, pairedSkew n d h c = 0 := by
      intro c
      simpa only [ha, zero_mul, zero_add, mul_eq_zero, ht, false_or] using heq c
    exact pairedSupport_constant_zero n h hsum (pairedSkew_kernel_constant n d hd h hzero)
  · have hdot : a * (∑ c, h c ^ 2) + t * (∑ c, h c * pairedSkew n d h c) = 0 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro c _
      have hh := congrArg (h c * ·) (heq c)
      nlinarith
    rw [pairedSkew_dot_self, mul_zero, add_zero] at hdot
    have hsq : ∑ c, h c ^ 2 = 0 := (mul_eq_zero.mp hdot).resolve_left ha
    have hpoint : ∀ c, h c ^ 2 = 0 := by
      intro c
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => sq_nonneg (h c))).mp hsq c (Finset.mem_univ c)
    funext c
    have hc := hpoint c
    exact sq_eq_zero_iff.mp hc

/-- The lottery tangent space, realized as an actual finite-dimensional submodule. -/
def probabilityTangent (C : Type*) [Fintype C] : Submodule ℝ (C → ℝ) where
  carrier := {h | ∑ c, h c = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all [Finset.sum_add_distrib]
  smul_mem' := by
    intro a h hh
    change ∑ c, a * h c = 0
    rw [← Finset.mul_sum, hh, mul_zero]

@[simp] theorem mem_probabilityTangent {C : Type*} [Fintype C] (h : C → ℝ) :
    h ∈ probabilityTangent C ↔ ∑ c, h c = 0 := Iff.rfl

noncomputable def pairedSkewLinear (n : ℕ) (d : ℝ) :
    (PairedSupport n → ℝ) →ₗ[ℝ] (PairedSupport n → ℝ) where
  toFun := pairedSkew n d
  map_add' := by
    intro h k
    funext c
    rcases c with _ | (i | i)
    · simp only [pairedSkew, Pi.add_apply]
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    all_goals simp [pairedSkew]; ring
  map_smul' := by
    intro a h
    funext c
    rcases c with _ | (i | i)
    · simp only [pairedSkew, Pi.smul_apply, smul_eq_mul]
      simp only [← mul_sub, ← Finset.mul_sum, RingHom.id_apply]
      ring
    all_goals simp [pairedSkew]; ring

noncomputable def pairedSkewTangent (n : ℕ) (d a t : ℝ) :
    probabilityTangent (PairedSupport n) →ₗ[ℝ] probabilityTangent (PairedSupport n) where
  toFun h := ⟨a • h.val + t • pairedSkewLinear n d h.val, by
    change ∑ c, (a * h.val c + t * pairedSkew n d h.val c) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      h.property, pairedSkew_sum]
    ring⟩
  map_add' h k := by apply Subtype.ext; simp [map_add, smul_add]; abel
  map_smul' s h := by
    apply Subtype.ext
    change a • (s • h.val) + t • (pairedSkewLinear n d (s • h.val)) =
      s • (a • h.val + t • pairedSkewLinear n d h.val)
    rw [map_smul, smul_add]
    simp only [smul_smul]
    congr 1 <;> rw [mul_comm]

theorem pairedSkewTangent_injective (n : ℕ) (d a t : ℝ) (hd : d ≠ 0) (ht : t ≠ 0) :
    Function.Injective (pairedSkewTangent n d a t) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro h hh
  apply Subtype.ext
  exact pairedSkew_scalar_injective_on_tangent n d a t hd ht h.val h.property
    (fun c => congrArg (fun k : probabilityTangent (PairedSupport n) => k.val c) hh)

/-- The auxiliary Jacobian is an invertible continuous linear operator on the
actual simplex tangent space, as required by the implicit function theorem. -/
theorem pairedSkewTangent_isInvertible (n : ℕ) (d a t : ℝ) (hd : d ≠ 0) (ht : t ≠ 0) :
    (pairedSkewTangent n d a t).toContinuousLinearMap.IsInvertible := by
  have hinj := pairedSkewTangent_injective n d a t hd ht
  have hbij : Function.Bijective (pairedSkewTangent n d a t) :=
    ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  exact ⟨(LinearEquiv.ofBijective (pairedSkewTangent n d a t) hbij).toContinuousLinearEquiv, rfl⟩

end OptimalG
