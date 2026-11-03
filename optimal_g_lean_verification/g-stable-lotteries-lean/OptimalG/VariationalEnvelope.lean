import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Essential-infimum envelopes of controls

The controls in (4.2) are only measurable in their low-rank coordinates before
regularity is established.  These lemmas prove directly that a uniform
Lipschitz estimate survives the essential infimum. No point evaluations of an
L-infinity equivalence class are required by the argument.
-/

namespace OptimalG.Variational

open MeasureTheory Filter
open scoped NNReal

variable {I X : Type*} [MeasurableSpace I] [PseudoMetricSpace X]
  {mu : Measure I} [NeZero mu]

/-- A real-valued control family is bounded outside a null set. -/
def EssentiallyBounded (f : I → ℝ) (mu : Measure I) : Prop :=
  ∃ B : ℝ, ∀ᵐ i ∂mu, |f i| ≤ B

omit [NeZero mu] in
theorem EssentiallyBounded.boundedBelow {f : I → ℝ}
    (hf : EssentiallyBounded f mu) :
    IsBoundedUnder (· ≥ ·) (ae mu) f := by
  obtain ⟨B, hB⟩ := hf
  apply isBoundedUnder_of_eventually_ge (a := -B)
  filter_upwards [hB] with i hi
  exact (abs_le.mp hi).1

omit [NeZero mu] in
theorem EssentiallyBounded.boundedAbove {f : I → ℝ}
    (hf : EssentiallyBounded f mu) :
    IsBoundedUnder (· ≤ ·) (ae mu) f := by
  obtain ⟨B, hB⟩ := hf
  apply isBoundedUnder_of_eventually_le (a := B)
  filter_upwards [hB] with i hi
  exact (abs_le.mp hi).2

omit [NeZero mu] in
theorem EssentiallyBounded.const (c : ℝ) :
    EssentiallyBounded (fun _ : I => c) mu :=
  ⟨|c|, Filter.Eventually.of_forall (fun _ => le_rfl)⟩

omit [NeZero mu] in
theorem EssentiallyBounded.add {f g : I → ℝ}
    (hf : EssentiallyBounded f mu) (hg : EssentiallyBounded g mu) :
    EssentiallyBounded (fun i => f i + g i) mu := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  refine ⟨B + C, ?_⟩
  filter_upwards [hB, hC] with i hi hci
  exact (abs_add_le _ _).trans (add_le_add hi hci)

omit [NeZero mu] in
theorem EssentiallyBounded.neg {f : I → ℝ} (hf : EssentiallyBounded f mu) :
    EssentiallyBounded (fun i => -f i) mu := by
  simpa only [EssentiallyBounded, abs_neg] using hf

omit [NeZero mu] in
theorem EssentiallyBounded.sub {f g : I → ℝ}
    (hf : EssentiallyBounded f mu) (hg : EssentiallyBounded g mu) :
    EssentiallyBounded (fun i => f i - g i) mu := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

omit [NeZero mu] in
theorem EssentiallyBounded.mul {f g : I → ℝ}
    (hf : EssentiallyBounded f mu) (hg : EssentiallyBounded g mu) :
    EssentiallyBounded (fun i => f i * g i) mu := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨C, hC⟩ := hg
  refine ⟨|B| * |C|, ?_⟩
  filter_upwards [hB, hC] with i hi hci
  rw [abs_mul]
  exact mul_le_mul (hi.trans (le_abs_self B)) (hci.trans (le_abs_self C))
    (abs_nonneg _) (abs_nonneg _)

omit [NeZero mu] in
theorem EssentiallyBounded.div_of_abs_lower {f g : I → ℝ}
    (hf : EssentiallyBounded f mu) (delta : ℝ) (hd : 0 < delta)
    (hg : ∀ᵐ i ∂mu, delta ≤ |g i|) :
    EssentiallyBounded (fun i => f i / g i) mu := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨|B| / delta, ?_⟩
  filter_upwards [hB, hg] with i hi hgi
  rw [abs_div]
  apply (div_le_div_iff₀ (hd.trans_le hgi) hd).mpr
  have hbi := hi.trans (le_abs_self B)
  have h1 := mul_le_mul_of_nonneg_right hbi hd.le
  have h2 := mul_le_mul_of_nonneg_left hgi (abs_nonneg B)
  exact h1.trans h2

/-- Uniform one-sided perturbations of controls bound the change in their
essential infima. This works without continuity in the control parameter. -/
theorem essInf_le_add_of_ae_le {f g : I → ℝ} (c : ℝ)
    (hf : EssentiallyBounded f mu) (hg : EssentiallyBounded g mu)
    (hfg : ∀ᵐ i ∂mu, f i ≤ g i + c) :
    essInf f mu ≤ essInf g mu + c := by
  have hlow := ae_essInf_le hf.boundedBelow
  have hshift : ∀ᵐ i ∂mu, essInf f mu - c ≤ g i := by
    filter_upwards [hlow, hfg] with i hi hfi
    linarith
  have h := le_essInf_of_ae_le (essInf f mu - c) hshift
    hg.boundedAbove.isCoboundedUnder_ge
  linarith

/-- The essential infimum inherits a common Lipschitz constant. -/
theorem lipschitz_essInf (H : X → I → ℝ) (K : ℝ≥0)
    (hbounded : ∀ x, EssentiallyBounded (H x) mu)
    (hlip : ∀ x y, ∀ᵐ i ∂mu, H x i ≤ H y i + K * dist x y) :
    LipschitzWith K (fun x => essInf (H x) mu) := by
  apply LipschitzWith.of_le_add_mul K
  intro x y
  exact essInf_le_add_of_ae_le (K * dist x y)
    (hbounded x) (hbounded y) (hlip x y)

omit [PseudoMetricSpace X] [NeZero mu] in
/-- Changing any of the controls on a null set changes no envelope value. -/
theorem essential_envelope_congr (H G : X → I → ℝ)
    (h : ∀ x, H x =ᵐ[mu] G x) :
    (fun x => essInf (H x) mu) = (fun x => essInf (G x) mu) := by
  funext x
  exact essInf_congr_ae (h x)

/-- A bounded measurable family of affine functions of the state has a
Lipschitz essential-infimum envelope. This is the state-variable estimate
needed for (4.3). -/
theorem lipschitz_affine_essInf (A B : I → ℝ) (K : ℝ≥0)
    (hA : ∀ᵐ i ∂mu, |A i| ≤ K)
    (hB : EssentiallyBounded B mu) :
    LipschitzWith K (fun u : ℝ => essInf (fun i => A i * u + B i) mu) := by
  apply lipschitz_essInf (fun u i => A i * u + B i) K
  · intro u
    obtain ⟨C, hC⟩ := hB
    refine ⟨K * |u| + C, ?_⟩
    filter_upwards [hA, hC] with i hi hci
    calc
      |A i * u + B i| ≤ |A i| * |u| + |B i| := by
        simpa [abs_mul] using abs_add_le (A i * u) (B i)
      _ ≤ K * |u| + C := add_le_add
        (mul_le_mul_of_nonneg_right hi (abs_nonneg u)) hci
  · intro u v
    filter_upwards [hA] with i hi
    have hmul := mul_le_mul_of_nonneg_right hi (abs_nonneg (u - v))
    have h := le_trans (le_abs_self (A i * (u - v)))
      ((abs_mul (A i) (u - v)).le.trans hmul)
    rw [Real.dist_eq]
    nlinarith

/-- A bounded family of affine functions in two feature coordinates has a
continuous envelope. Composing with `(z,z²)` covers the quadratic time
coordinate of the rational controls. -/
theorem continuous_affine2_essInf (A B C : I → ℝ)
    (hA : EssentiallyBounded A mu) (hB : EssentiallyBounded B mu)
    (hC : EssentiallyBounded C mu) :
    Continuous (fun v : ℝ × ℝ =>
      essInf (fun i => A i * v.1 + B i * v.2 + C i) mu) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  let K : ℝ≥0 := ⟨|a| + |b|, add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  apply (lipschitz_essInf _ K ?_ ?_).continuous
  · intro v
    exact ((EssentiallyBounded.mul ⟨a, ha⟩ (EssentiallyBounded.const v.1)).add
      (EssentiallyBounded.mul ⟨b, hb⟩ (EssentiallyBounded.const v.2))).add hC
  · intro v w
    filter_upwards [ha, hb] with i hai hbi
    have hfst : |v.1 - w.1| ≤ dist v w := by
      simpa only [Prod.dist_eq, Real.dist_eq] using
        (le_max_left (|v.1 - w.1|) (|v.2 - w.2|))
    have hsnd : |v.2 - w.2| ≤ dist v w := by
      simpa only [Prod.dist_eq, Real.dist_eq] using
        (le_max_right (|v.1 - w.1|) (|v.2 - w.2|))
    have h1 : A i * (v.1 - w.1) ≤ |a| * dist v w := by
      calc
        _ ≤ |A i * (v.1 - w.1)| := le_abs_self _
        _ = |A i| * |v.1 - w.1| := abs_mul _ _
        _ ≤ |a| * dist v w := mul_le_mul
          (hai.trans (le_abs_self a)) hfst (abs_nonneg _) (abs_nonneg _)
    have h2 : B i * (v.2 - w.2) ≤ |b| * dist v w := by
      calc
        _ ≤ |B i * (v.2 - w.2)| := le_abs_self _
        _ = |B i| * |v.2 - w.2| := abs_mul _ _
        _ ≤ |b| * dist v w := mul_le_mul
          (hbi.trans (le_abs_self b)) hsnd (abs_nonneg _) (abs_nonneg _)
    change A i * v.1 + B i * v.2 + C i ≤
      A i * w.1 + B i * w.2 + C i + (|a| + |b|) * dist v w
    nlinarith

end OptimalG.Variational
