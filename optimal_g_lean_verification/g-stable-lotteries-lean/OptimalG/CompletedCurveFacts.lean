import OptimalG.BinaryCurveGeometry
import OptimalG.Certificates.SmallMassExpressions
import OptimalG.VariationalSlackArea

/-! Head normalization and the rounded reference bounds are consequences of
the actual completed geometry and the original localized primitive bound.
These facts connect the variational construction to the finite verifier boxes. -/
namespace OptimalG
open Set MeasureTheory

namespace BinaryCurveGeometry

theorem initial_eq {phi : ℝ → ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c) :
    phi 0 = Certificates.SmallMassExpressions.initial lam S := by
  have hh := g.head (527/2000) ⟨by norm_num,le_rfl⟩
  have hc := g.cap_score (527/2000) ⟨le_rfl,by linarith only [g.contact_mem.1]⟩
  have hj : Certificates.SmallMassExpressions.initial lam S+
      Certificates.SmallMassExpressions.slope lam S*(527/2000)=
      Variational.capScore lam S (527/2000) :=
    headScore_at_join _ _ _ (by norm_num)
  linarith only [hh,hc,hj]

/-- The exact original reference rank gives both rounded reference bounds
used by the binary and mixed certificates, by an integral triangle estimate
and monotonicity. The statement covers the whole later low-rank interval. -/
theorem reference_bounds {phi : ℝ → ℝ} {lam S slope c : ℝ}
    (g : BinaryCurveGeometry phi lam S slope c) (h : VerifierCurve phi lam)
    (harea : binarySlackArea phi lam S (0.34854007977695545 : ℝ) <
      (0.00000008688098 : ℝ)) :
    ∀ r ∈ Icc (0.34854007977695545 : ℝ) (31/40),
      binarySlackArea phi lam S r ≤ 87/1000000000 ∧
      scoreDefect phi lam r ≤ 3/12500 := by
  let a : ℝ := 0.34854007977695545
  have ha0 : 0 ≤ a := by norm_num [a]
  have hac : c ≤ a := by dsimp [a]; linarith only [g.contact_mem.2]
  have ha38 : a ≤ 19/50 := by norm_num [a]
  have harea38 : binarySlackArea phi lam S (19/50)=0 := by
    unfold binarySlackArea
    rw [g.line_primitive (19/50) ⟨by norm_num,by norm_num⟩]
    ring
  have hscore : scoreDefect phi lam a < 3/12500 := by
    apply Variational.slack_lt_of_area_bound (f:=scoreDefect phi lam)
      (a:=a) (b:=19/50) (r:=a) (L:=309/1000)
      (by norm_num) (by norm_num) ⟨le_rfl,ha38⟩
      (by norm_num [a])
      ((h.scoreDefect_continuous.mono
        (Icc_subset_Icc ha0 (by norm_num : (19/50 : ℝ) ≤ 1))).intervalIntegrable_of_Icc ha38)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact h.scoreDefect_nonneg ⟨ha0.trans hr.1,hr.2.trans (by norm_num)⟩
    · intro r hr
      have hh := g.post_slope a ⟨hac,by norm_num [a]⟩ r
        ⟨hac.trans hr.1,by dsimp [a] at hr; linarith only [hr.2]⟩ hr.1
      unfold scoreDefect
      linarith only [hh]
    · rw [←h.binarySlackArea_difference (S:=S) ha0 ha38 (by norm_num),harea38,sub_zero]
      dsimp [a]
      norm_num
      linarith only [harea]
  intro r hr
  have hrr : r ∈ Icc (0 : ℝ) 1 :=
    ⟨ha0.trans hr.1,hr.2.trans (by norm_num)⟩
  have ha1 : a ∈ Icc (0 : ℝ) 1 := ⟨ha0,by norm_num [a]⟩
  have harea' := h.binarySlackArea_antitone S ha1 hrr hr.1
  dsimp only [a] at harea'
  have hscore' := g.defect_antitone
    ⟨ha0,by norm_num [a]⟩ ⟨hrr.1,hr.2⟩ hr.1
  exact ⟨by linarith only [harea',harea],hscore'.trans hscore.le⟩

/-- Rewrite the variational localization using the actual completed primitive.
The measured low score itself need not be pointwise continuous. -/
theorem reference_bounds_of_low_primitive {phi : ℝ → ℝ} {lam slope c : ℝ}
    {d : Variational.LowRankData}
    (g : BinaryCurveGeometry phi lam d.S slope c) (h : VerifierCurve phi lam)
    (hprimitive : ∀ r ∈ Icc (527/2000 : ℝ) Variational.xHi,
      curvePrimitive phi r=Variational.primitive lam d r)
    (harea : d.S-Variational.quadratic lam 0.34854007977695545+
      Variational.lowPrimitive lam d 0.34854007977695545 < (0.00000008688098 : ℝ)) :
    (binarySlackArea phi lam d.S (348541/1000000) ≤ 87/1000000000 ∧
      scoreDefect phi lam (348541/1000000) ≤ 3/12500) ∧
    (binarySlackArea phi lam d.S (7/20) ≤ 87/1000000000 ∧
      scoreDefect phi lam (7/20) ≤ 3/12500) := by
  have ha : binarySlackArea phi lam d.S (0.34854007977695545 : ℝ) <
      (0.00000008688098 : ℝ) := by
    unfold binarySlackArea
    rw [hprimitive _ ⟨by norm_num,by norm_num [Variational.xHi]⟩]
    simp only [Variational.primitive,
      if_neg (by norm_num [Variational.ell] : ¬(0.34854007977695545 : ℝ) ≤ Variational.ell),
      if_pos (by norm_num [Variational.tEnd] : (0.34854007977695545 : ℝ) ≤ Variational.tEnd)]
    linarith only [harea]
  have hh := g.reference_bounds h ha
  exact ⟨hh _ ⟨by norm_num,by norm_num⟩,hh _ ⟨by norm_num,by norm_num⟩⟩

end BinaryCurveGeometry
end OptimalG
