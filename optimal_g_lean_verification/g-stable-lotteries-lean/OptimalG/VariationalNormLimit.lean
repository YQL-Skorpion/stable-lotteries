import OptimalG.VariationalFrozenLimit

/-! Uniform almost-everywhere convergence and continuity of essential infima. -/
namespace OptimalG.Variational
open MeasureTheory Filter Set
open scoped Topology
variable {I : Type*} [MeasurableSpace I] {μ : Measure I}

/-- Uniform error bounds outside null sets, with errors tending to zero. -/
def AENormTendsto (fn : ℕ → I → ℝ) (f : I → ℝ) (μ : Measure I) : Prop :=
  ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ n, 0 ≤ e n ∧ ∀ᵐ i ∂μ, |fn n i-f i| ≤ e n

theorem AENormTendsto.refl (f : I → ℝ) : AENormTendsto (fun _ => f) f μ := by
  refine ⟨fun _ => 0, tendsto_const_nhds, fun _ => ⟨le_rfl, ?_⟩⟩
  exact Eventually.of_forall (fun _ => by simp)

theorem AENormTendsto.of_scalar {an : ℕ → ℝ} {a : ℝ} (ha : Tendsto an atTop (𝓝 a)) :
    AENormTendsto (fun n (_ : I) => an n) (fun _ => a) μ := by
  refine ⟨fun n => |an n-a|, ?_, fun n => ⟨abs_nonneg _, Eventually.of_forall fun _ => le_rfl⟩⟩
  simpa only [sub_self, abs_zero] using (ha.sub_const a).abs

theorem AENormTendsto.congr {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (h : AENormTendsto fn f μ) (hn : ∀ n, fn n =ᵐ[μ] gn n) (hfg : f =ᵐ[μ] g) :
    AENormTendsto gn g μ := by
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, fun n => ⟨(hb n).1, ?_⟩⟩
  filter_upwards [(hb n).2, hn n, hfg] with i hi hni hfi
  simpa only [hni, hfi] using hi

theorem AENormTendsto.add {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : AENormTendsto fn f μ) (hg : AENormTendsto gn g μ) :
    AENormTendsto (fun n i => fn n i+gn n i) (fun i => f i+g i) μ := by
  obtain ⟨e, he, heb⟩ := hf
  obtain ⟨d, hd, hdb⟩ := hg
  refine ⟨fun n => e n+d n, by simpa using he.add hd, fun n => ⟨add_nonneg (heb n).1 (hdb n).1, ?_⟩⟩
  filter_upwards [(heb n).2, (hdb n).2] with i hei hdi
  calc
    _ = |(fn n i-f i)+(gn n i-g i)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hei hdi)

theorem AENormTendsto.neg {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) : AENormTendsto (fun n i => -fn n i) (fun i => -f i) μ := by
  obtain ⟨e, he, heb⟩ := hf
  refine ⟨e, he, fun n => ⟨(heb n).1, ?_⟩⟩
  filter_upwards [(heb n).2] with i hi
  simpa only [neg_sub_neg, abs_sub_comm] using hi

theorem AENormTendsto.sub {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : AENormTendsto fn f μ) (hg : AENormTendsto gn g μ) :
    AENormTendsto (fun n i => fn n i-gn n i) (fun i => f i-g i) μ := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem AENormTendsto.mul {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : AENormTendsto fn f μ) (hg : AENormTendsto gn g μ)
    (hfb : EssentiallyBounded f μ) (hgb : EssentiallyBounded g μ) :
    AENormTendsto (fun n i => fn n i*gn n i) (fun i => f i*g i) μ := by
  obtain ⟨e, he, heb⟩ := hf
  obtain ⟨d, hd, hdb⟩ := hg
  obtain ⟨B, hB⟩ := hfb
  obtain ⟨C, hC⟩ := hgb
  refine ⟨fun n => e n * (|C| + d n) + |B| * d n, ?_,
    fun n => ⟨by have := (heb n).1; have := (hdb n).1; positivity, ?_⟩⟩
  · simpa using (he.mul (tendsto_const_nhds.add hd)).add (hd.const_mul |B|)
  · filter_upwards [(heb n).2, (hdb n).2, hB, hC] with i hei hdi hBi hCi
    have hgn : |gn n i| ≤ |C| + d n := by
      have htri := abs_add_le (gn n i-g i) (g i)
      rw [sub_add_cancel] at htri
      linarith [le_abs_self C]
    calc
      _ = |(fn n i-f i)*gn n i+f i*(gn n i-g i)| := by congr 1; ring
      _ ≤ |fn n i-f i| * |gn n i| + |f i| * |gn n i-g i| := by
        simpa only [abs_mul] using abs_add_le ((fn n i-f i)*gn n i) (f i*(gn n i-g i))
      _ ≤ _ := add_le_add (mul_le_mul hei hgn (abs_nonneg _) (heb n).1)
        (mul_le_mul (hBi.trans (le_abs_self B)) hdi (abs_nonneg _) (abs_nonneg _))

theorem AENormTendsto.inv {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) {δ : ℝ} (hδ : 0 < δ)
    (hn : ∀ n, ∀ᵐ i ∂μ, δ ≤ |fn n i|) (h0 : ∀ᵐ i ∂μ, δ ≤ |f i|) :
    AENormTendsto (fun n i => (fn n i)⁻¹) (fun i => (f i)⁻¹) μ := by
  obtain ⟨e, he, heb⟩ := hf
  refine ⟨fun n => e n/(δ*δ), by simpa using he.div_const (δ*δ),
    fun n => ⟨div_nonneg (heb n).1 (mul_pos hδ hδ).le, ?_⟩⟩
  filter_upwards [(heb n).2, hn n, h0] with i hei hni hfi
  have hn0 : fn n i ≠ 0 := by intro h; simp [h] at hni; linarith
  have hf0 : f i ≠ 0 := by intro h; simp [h] at hfi; linarith
  rw [inv_sub_inv hn0 hf0, abs_div, abs_mul, abs_sub_comm]
  exact div_le_div₀ (heb n).1 hei (mul_pos hδ hδ) (mul_le_mul hni hfi hδ.le (abs_nonneg _))

theorem AENormTendsto.div {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : AENormTendsto fn f μ) (hg : AENormTendsto gn g μ)
    (hfb : EssentiallyBounded f μ) {δ : ℝ} (hδ : 0 < δ)
    (hn : ∀ n, ∀ᵐ i ∂μ, δ ≤ |gn n i|) (h0 : ∀ᵐ i ∂μ, δ ≤ |g i|) :
    AENormTendsto (fun n i => fn n i/gn n i) (fun i => f i/g i) μ := by
  have hgb : EssentiallyBounded (fun i => (g i)⁻¹) μ := by
    simpa only [one_div] using (EssentiallyBounded.const (mu := μ) 1).div_of_abs_lower δ hδ h0
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hδ hn h0) hfb hgb

theorem AENormTendsto.comp {J : Type*} [MeasurableSpace J] {ν : Measure J}
    {fn : ℕ → I → ℝ} {f : I → ℝ} (hf : AENormTendsto fn f μ) (T : J → I)
    (hlift : ∀ P : I → Prop, (∀ᵐ i ∂μ, P i) → ∀ᵐ j ∂ν, P (T j)) :
    AENormTendsto (fun n j => fn n (T j)) (fun j => f (T j)) ν := by
  obtain ⟨e, he, hb⟩ := hf
  exact ⟨e, he, fun n => ⟨(hb n).1, hlift _ (hb n).2⟩⟩

theorem AENormTendsto.essInf_tendsto [NeZero μ] {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) (hnb : ∀ n, EssentiallyBounded (fn n) μ)
    (hb : EssentiallyBounded f μ) :
    Tendsto (fun n => essInf (fn n) μ) atTop (𝓝 (essInf f μ)) := by
  obtain ⟨e, he, heb⟩ := hf
  have hz : Tendsto (fun n => essInf (fn n) μ-essInf f μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun n => ?_) he
    have hupper := essInf_le_add_of_ae_le (e n) (hnb n) hb ((heb n).2.mono fun i hi => by
      linarith [le_abs_self (fn n i-f i)])
    have hlower := essInf_le_add_of_ae_le (e n) hb (hnb n) ((heb n).2.mono fun i hi => by
      linarith [neg_abs_le (fn n i-f i)])
    simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨by linarith, by linarith⟩ :
      |essInf (fn n) μ-essInf f μ| ≤ e n)
  simpa only [sub_add_cancel, zero_add] using hz.add_const (essInf f μ)

theorem AENormTendsto.mul_const {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) (c : ℝ) :
    AENormTendsto (fun n i => fn n i*c) (fun i => f i*c) μ := by
  obtain ⟨e, he, heb⟩ := hf
  refine ⟨fun n => e n * |c|, by simpa using he.mul_const |c|,
    fun n => ⟨mul_nonneg (heb n).1 (abs_nonneg _), ?_⟩⟩
  filter_upwards [(heb n).2] with i hi
  rw [← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)

theorem AENormTendsto.const_mul {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) (c : ℝ) :
    AENormTendsto (fun n i => c*fn n i) (fun i => c*f i) μ := by
  simpa only [mul_comm] using hf.mul_const c

theorem AENormTendsto.div_const {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : AENormTendsto fn f μ) (c : ℝ) :
    AENormTendsto (fun n i => fn n i/c) (fun i => f i/c) μ := by
  simpa only [div_eq_mul_inv] using hf.mul_const c⁻¹

theorem AENormTendsto.ite {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : AENormTendsto fn f μ) (hg : AENormTendsto gn g μ) (P : I → Prop) [DecidablePred P] :
    AENormTendsto (fun n i => if P i then fn n i else gn n i)
      (fun i => if P i then f i else g i) μ := by
  obtain ⟨e, he, heb⟩ := hf
  obtain ⟨d, hd, hdb⟩ := hg
  refine ⟨fun n => e n+d n, by simpa using he.add hd,
    fun n => ⟨add_nonneg (heb n).1 (hdb n).1, ?_⟩⟩
  filter_upwards [(heb n).2, (hdb n).2] with i hi hgi
  split_ifs <;> linarith [(heb n).1, (hdb n).1]

structure BoundedAENormTendsto (fn : ℕ → I → ℝ) (f : I → ℝ) (μ : Measure I) : Prop where
  converges : AENormTendsto fn f μ
  bounded : EssentiallyBounded f μ

theorem BoundedAENormTendsto.refl (f : I → ℝ) (hf : EssentiallyBounded f μ) :
    BoundedAENormTendsto (fun _ => f) f μ := ⟨AENormTendsto.refl f, hf⟩
theorem BoundedAENormTendsto.scalar {an : ℕ → ℝ} {a : ℝ} (ha : Tendsto an atTop (𝓝 a)) :
    BoundedAENormTendsto (fun n (_ : I) => an n) (fun _ => a) μ :=
  ⟨AENormTendsto.of_scalar ha, EssentiallyBounded.const a⟩
theorem BoundedAENormTendsto.add {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (hg : BoundedAENormTendsto gn g μ) :
    BoundedAENormTendsto (fun n i => fn n i+gn n i) (fun i => f i+g i) μ :=
  ⟨hf.converges.add hg.converges, hf.bounded.add hg.bounded⟩
theorem BoundedAENormTendsto.sub {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (hg : BoundedAENormTendsto gn g μ) :
    BoundedAENormTendsto (fun n i => fn n i-gn n i) (fun i => f i-g i) μ :=
  ⟨hf.converges.sub hg.converges, hf.bounded.sub hg.bounded⟩
theorem BoundedAENormTendsto.mul {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (hg : BoundedAENormTendsto gn g μ) :
    BoundedAENormTendsto (fun n i => fn n i*gn n i) (fun i => f i*g i) μ :=
  ⟨hf.converges.mul hg.converges hf.bounded hg.bounded, hf.bounded.mul hg.bounded⟩
theorem BoundedAENormTendsto.const_mul {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (c : ℝ) :
    BoundedAENormTendsto (fun n i => c*fn n i) (fun i => c*f i) μ :=
  (BoundedAENormTendsto.scalar (tendsto_const_nhds (x := c))).mul hf

theorem BoundedAENormTendsto.div_const {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (c : ℝ) :
    BoundedAENormTendsto (fun n i => fn n i/c) (fun i => f i/c) μ := by
  simpa only [div_eq_mul_inv] using hf.mul (BoundedAENormTendsto.scalar (tendsto_const_nhds (x := c⁻¹)))
theorem BoundedAENormTendsto.neg {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) :
    BoundedAENormTendsto (fun n i => -fn n i) (fun i => -f i) μ :=
  ⟨hf.converges.neg, hf.bounded.neg⟩
theorem BoundedAENormTendsto.pow_two {fn : ℕ → I → ℝ} {f : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) :
    BoundedAENormTendsto (fun n i => fn n i ^ 2) (fun i => f i ^ 2) μ := by
  simpa only [_root_.pow_two] using hf.mul hf

theorem BoundedAENormTendsto.div {fn gn : ℕ → I → ℝ} {f g : I → ℝ}
    (hf : BoundedAENormTendsto fn f μ) (hg : BoundedAENormTendsto gn g μ)
    {δ : ℝ} (hδ : 0 < δ) (hn : ∀ n, ∀ᵐ i ∂μ, δ ≤ |gn n i|)
    (h0 : ∀ᵐ i ∂μ, δ ≤ |g i|) :
    BoundedAENormTendsto (fun n i => fn n i/gn n i) (fun i => f i/g i) μ :=
  ⟨hf.converges.div hg.converges hf.bounded hδ hn h0, hf.bounded.div_of_abs_lower δ hδ h0⟩
end OptimalG.Variational
