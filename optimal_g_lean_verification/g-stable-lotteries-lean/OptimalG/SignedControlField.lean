import OptimalG.VariationalEnvelope

/-! Continuous control envelopes for signed scores. No positivity hypothesis is
needed for ODE existence; compact bounds give finite Lipschitz constants. -/
namespace OptimalG.Variational
open MeasureTheory Set
open scoped NNReal

variable {I : Type*} [MeasurableSpace I] {mu : Measure I} [NeZero mu]

theorem EssentiallyBounded.comp_lipschitz {f : I → ℝ} {J : ℝ → ℝ} {K : ℝ≥0}
    (hf : EssentiallyBounded f mu) (hJ : LipschitzWith K J) :
    EssentiallyBounded (fun i => J (f i)) mu := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|J 0| + K* |B|, ?_⟩
  filter_upwards [hB] with i hi
  have hd := hJ.dist_le_mul (f i) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at hd
  have hm := mul_le_mul_of_nonneg_left (hi.trans (le_abs_self B)) K.coe_nonneg
  have ht := abs_add_le (J (f i)-J 0) (J 0)
  rw [sub_add_cancel] at ht
  linarith

noncomputable def signedControlH (lam : ℝ) (J : ℝ → ℝ)
    (A B p : I → ℝ) (z u : ℝ) (i : I) : ℝ :=
  A i*u - B i*(z-lam) - A i*J (z-p i)

noncomputable def signedVectorField (lam : ℝ) (J : ℝ → ℝ)
    (A B p : I → ℝ) (mu : Measure I) (z u : ℝ) : ℝ :=
  min (lam-z) (essInf (signedControlH lam J A B p z u) mu)

theorem signedControlH_bounded {lam : ℝ} {J : ℝ → ℝ}
    {A B p : I → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hA : EssentiallyBounded A mu)
    (hB : EssentiallyBounded B mu) (hp : EssentiallyBounded p mu) (z u : ℝ) :
    EssentiallyBounded (signedControlH lam J A B p z u) mu := by
  exact ((hA.mul (EssentiallyBounded.const u)).sub
    (hB.mul (EssentiallyBounded.const (z-lam)))).sub
    (hA.mul (((EssentiallyBounded.const z).sub hp).comp_lipschitz hJ))

theorem signedVectorField_state_lipschitz {lam : ℝ} {J : ℝ → ℝ}
    {A B p : I → ℝ} {K KA : ℝ≥0}
    (hJ : LipschitzWith K J) (hA : ∀ᵐ i ∂mu, |A i| ≤ KA)
    (hB : EssentiallyBounded B mu) (hp : EssentiallyBounded p mu) (z : ℝ) :
    LipschitzWith KA (signedVectorField lam J A B p mu z) := by
  have hbase := signedControlH_bounded (lam := lam) hJ ⟨KA, hA⟩ hB hp z 0
  have hh := lipschitz_affine_essInf A (signedControlH lam J A B p z 0) KA hA hbase
  have he (u : ℝ) :
      (fun i => A i*u+signedControlH lam J A B p z 0 i) = signedControlH lam J A B p z u := by
    funext i
    unfold signedControlH
    ring
  have hh' : LipschitzWith KA (fun u => essInf (signedControlH lam J A B p z u) mu) := by
    simpa only [he] using hh
  exact hh'.const_min (lam-z)

theorem signedVectorField_time_lipschitz {lam : ℝ} {J : ℝ → ℝ}
    {A B p : I → ℝ} {K KA KB : ℝ≥0}
    (hJ : LipschitzWith K J)
    (hA : ∀ᵐ i ∂mu, |A i| ≤ KA) (hB : ∀ᵐ i ∂mu, |B i| ≤ KB)
    (hp : EssentiallyBounded p mu) (u : ℝ) :
    LipschitzWith (max 1 (KB+KA*K)) (fun z => signedVectorField lam J A B p mu z u) := by
  have he : LipschitzWith (KB+KA*K)
      (fun z => essInf (signedControlH lam J A B p z u) mu) := by
    apply lipschitz_essInf (fun z i => signedControlH lam J A B p z u i) (KB+KA*K)
    · intro z
      exact signedControlH_bounded hJ ⟨KA,hA⟩ ⟨KB,hB⟩ hp z u
    · intro z w
      filter_upwards [hA,hB] with i hAi hBi
      have hj := hJ.dist_le_mul (z-p i) (w-p i)
      rw [Real.dist_eq, Real.dist_eq] at hj
      have hd : z-p i-(w-p i)=z-w := by ring
      rw [hd] at hj
      have h1 := mul_le_mul_of_nonneg_right hBi (abs_nonneg (z-w))
      have h2 := mul_le_mul hAi hj (abs_nonneg _) KA.coe_nonneg
      have hh := abs_add_le (-B i*(z-w)) (-A i*(J (z-p i)-J (w-p i)))
      rw [abs_mul, abs_neg, abs_mul, abs_neg] at hh
      have hdiff : signedControlH lam J A B p z u i - signedControlH lam J A B p w u i =
          -B i*(z-w) + -A i*(J (z-p i)-J (w-p i)) := by
        unfold signedControlH
        ring
      have hbound : signedControlH lam J A B p z u i - signedControlH lam J A B p w u i ≤
          |B i| * |z-w| + |A i| * |J (z-p i)-J (w-p i)| := by
        calc
          _ ≤ |signedControlH lam J A B p z u i - signedControlH lam J A B p w u i| := le_abs_self _
          _ = |-B i*(z-w) + -A i*(J (z-p i)-J (w-p i))| := congrArg abs hdiff
          _ ≤ _ := hh
      rw [Real.dist_eq]
      norm_num only [NNReal.coe_add, NNReal.coe_mul]
      nlinarith only [hbound,h1,h2]
  have hl : LipschitzWith 1 (fun z : ℝ => lam-z) := by
    apply LipschitzWith.of_le_add
    intro z w
    rw [Real.dist_eq]
    have hh := neg_le_abs (z-w)
    linarith
  exact hl.min he

end OptimalG.Variational
