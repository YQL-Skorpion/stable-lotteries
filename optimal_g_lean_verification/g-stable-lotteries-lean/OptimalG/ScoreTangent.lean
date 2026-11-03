import OptimalG.ProfileJacobian

/-! # Centered score projection and the actual simplex tangent Jacobian -/

namespace OptimalG
open scoped BigOperators

/-- Subtracting the coordinate mean projects onto the probability tangent. -/
noncomputable def probabilityProjection {m : ℕ} [NeZero m] :
    (Fin m → ℝ) →ₗ[ℝ] probabilityTangent (Fin m) where
  toFun h := ⟨fun a => h a - (∑ b, h b) / (m : ℝ), by
    change ∑ a, (h a - (∑ b, h b) / (m : ℝ)) = 0
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring⟩
  map_add' h k := by
    apply Subtype.ext
    funext a
    simp [Finset.sum_add_distrib, add_div]
    ring
  map_smul' c h := by
    apply Subtype.ext
    funext a
    simp [← Finset.mul_sum]
    ring

noncomputable def probabilityProjectionContinuous {m : ℕ} [NeZero m] :
    (Fin m → ℝ) →L[ℝ] probabilityTangent (Fin m) := probabilityProjection.toContinuousLinearMap

@[simp] theorem probabilityProjection_val {m : ℕ} [NeZero m] (h : Fin m → ℝ) (a : Fin m) :
    (probabilityProjection h).val a = h a - (∑ b, h b) / (m : ℝ) := rfl

theorem probabilityProjection_tangent {m : ℕ} [NeZero m] (h : probabilityTangent (Fin m)) :
    probabilityProjection h.val = h := by
  apply Subtype.ext
  funext a
  have hs : ∑ b, h.val b = 0 := h.property
  simp only [probabilityProjection_val, hs, zero_div, sub_zero]

/-- Vanishing centered scores means all supported scores are equal. -/
theorem probabilityProjection_eq_zero_iff {m : ℕ} [NeZero m] (h : Fin m → ℝ) :
    probabilityProjection h = 0 ↔ ∀ a b, h a = h b := by
  constructor
  · intro hz a b
    have ha := congrArg (fun x : probabilityTangent (Fin m) => x.val a) hz
    have hb := congrArg (fun x : probabilityTangent (Fin m) => x.val b) hz
    change h a - (∑ c, h c) / (m : ℝ) = 0 at ha
    change h b - (∑ c, h c) / (m : ℝ) = 0 at hb
    linarith
  · intro hconstant
    apply Subtype.ext
    funext a
    change h a - (∑ c, h c) / (m : ℝ) = 0
    have hsum : ∑ c, h c = (m : ℝ) * h a := by
      simp only [hconstant _ a, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    rw [hsum]
    field_simp
    ring

/-- A stationary profile's actual score Jacobian restricted to the tangent. -/
noncomputable def profileTangentJacobian {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (u mean : ℝ)
    (hu : u ≠ 0)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (fun _ => u)) = mean) :
    probabilityTangent (Fin m) →ₗ[ℝ] probabilityTangent (Fin m) where
  toFun h := ⟨profileLotteryJacobian g orders w (fun _ => u) h.val,
    profileLotteryJacobian_maps_tangent g orders w u mean hu hstationary h.val h.property⟩
  map_add' h k := by apply Subtype.ext; exact map_add _ h.val k.val
  map_smul' c h := by apply Subtype.ext; exact map_smul _ c h.val

theorem profileTangentJacobian_isInvertible {V : Type*} [Fintype V] {m : ℕ}
    (g : ℝ → ℝ) (orders : V → Equiv.Perm (Fin m)) (w : V → ℝ) (u mean : ℝ)
    (hu : u ≠ 0)
    (hstationary : ∀ a, expectation w (fun v => scoreExtension g (orders v) a (fun _ => u)) = mean)
    (hinjective : ∀ h : Fin m → ℝ, (∑ a, h a) = 0 →
      profileLotteryJacobian g orders w (fun _ => u) h = 0 → h = 0) :
    (profileTangentJacobian g orders w u mean hu hstationary).toContinuousLinearMap.IsInvertible := by
  let A := profileTangentJacobian g orders w u mean hu hstationary
  have hi : Function.Injective A := by
    apply (injective_iff_map_eq_zero _).mpr
    intro h hh
    apply Subtype.ext
    exact hinjective h.val h.property (congrArg Subtype.val hh)
  have hbij : Function.Bijective A := ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨(LinearEquiv.ofBijective A hbij).toContinuousLinearEquiv, rfl⟩

end OptimalG
