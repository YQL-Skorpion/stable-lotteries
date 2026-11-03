import OptimalG.RankIntegral
import Mathlib.Data.ENNReal.Real

/-!
# Finite elections and the actual worst-case distortion

Elections have nonempty finite voter and candidate sets, represented by `Fin` types,
with equally weighted voters. A ranking is a permutation listed from worst to best.
Metrics are arbitrary pseudometrics on the disjoint union of voters and candidates.
This includes co-located points and zero optimal social cost.
-/

namespace OptimalG

open Set MeasureTheory
open scoped BigOperators ENNReal

structure Lottery (m : ℕ) where
  weight : Fin m → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

structure Election where
  voterCount : ℕ
  candidateCount : ℕ
  voters_pos : 0 < voterCount
  candidates_pos : 0 < candidateCount
  order : Fin voterCount → Equiv.Perm (Fin candidateCount)

namespace Election

abbrev Voter (E : Election) := Fin E.voterCount
abbrev Candidate (E : Election) := Fin E.candidateCount
abbrev Point (E : Election) := E.Voter ⊕ E.Candidate
abbrev Metric (E : Election) := PseudoMetricSpace E.Point

instance candidateCount_neZero (E : Election) : NeZero E.candidateCount :=
  ⟨Nat.ne_of_gt E.candidates_pos⟩

instance voterCount_neZero (E : Election) : NeZero E.voterCount :=
  ⟨Nat.ne_of_gt E.voters_pos⟩

noncomputable def voterWeight (E : Election) (_v : E.Voter) : ℝ :=
  1 / E.voterCount

theorem voterWeight_nonneg (E : Election) (v : E.Voter) : 0 ≤ E.voterWeight v := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem voterWeight_total (E : Election) : ∑ v, E.voterWeight v = 1 := by
  have hn : (E.voterCount : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt E.voters_pos
  simp [voterWeight, hn]

def ordinalRank (E : Election) (v : E.Voter) (a : E.Candidate) : ℕ :=
  ((E.order v).symm a).val

noncomputable def activation (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (v : E.Voter) (a : E.Candidate) : ℝ :=
  orderedActivation g D.weight (E.order v) a

def Stable (E : Election) (g : ℝ → ℝ) (D : Lottery E.candidateCount) : Prop :=
  ∀ a, expectation E.voterWeight (fun v => E.activation g D v a) ≤
    ∫ r in (0 : ℝ)..1, g r

theorem supported_stationarity (E : Election) (g : ℝ → ℝ)
    (D : Lottery E.candidateCount) (hg : ContinuousOn g (Icc 0 1))
    (hstable : E.Stable g D) (a : E.Candidate) (ha : 0 < D.weight a) :
    expectation E.voterWeight (fun v => E.activation g D v a) =
      ∫ r in (0 : ℝ)..1, g r := by
  exact OptimalG.supported_stationarity g D.weight E.voterWeight E.order hg
    D.nonneg D.total E.voterWeight_total hstable a ha

def Consistent (E : Election) (d : E.Metric) : Prop :=
  letI := d
  ∀ v b c, E.ordinalRank v c ≤ E.ordinalRank v b →
    dist (Sum.inl v) (Sum.inr b) ≤ dist (Sum.inl v) (Sum.inr c)

noncomputable def candidateCost (E : Election) (d : E.Metric) (a : E.Candidate) : ℝ :=
  letI := d
  expectation E.voterWeight (fun v => dist (Sum.inl v) (Sum.inr a))

noncomputable def lotteryCost (E : Election) (d : E.Metric)
    (D : Lottery E.candidateCount) : ℝ := expectation D.weight (E.candidateCost d)

theorem candidateCost_nonneg (E : Election) (d : E.Metric) (a : E.Candidate) :
    0 ≤ E.candidateCost d a := by
  letI := d
  unfold candidateCost expectation
  exact Finset.sum_nonneg (fun v _ => mul_nonneg (E.voterWeight_nonneg v)
    (dist_nonneg (x := (Sum.inl v : E.Point)) (y := Sum.inr a)))

theorem lotteryCost_nonneg (E : Election) (d : E.Metric) (D : Lottery E.candidateCount) :
    0 ≤ E.lotteryCost d D := by
  unfold lotteryCost expectation
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (D.nonneg a) (E.candidateCost_nonneg d a))

theorem lotteryCost_eq_voter_average (E : Election) (d : E.Metric)
    (D : Lottery E.candidateCount) :
    E.lotteryCost d D =
      letI := d
      expectation E.voterWeight
        (fun v => expectation D.weight (fun a => dist (Sum.inl v) (Sum.inr a))) := by
  letI := d
  exact expectation_commute E.voterWeight D.weight _

end Election

/-- The paper's class of continuous activations into `[0,1]`. Values outside
that interval are immaterial because all rank arguments lie inside it. -/
def AdmissibleActivation (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Icc 0 1) ∧ MapsTo g (Icc 0 1) (Icc 0 1)

/-- Extended ratio with the usual harmless convention 0/0=1 and positive/0=∞. -/
noncomputable def costRatio (cost optimum : ℝ) : ℝ≥0∞ :=
  if optimum = 0 then (if cost = 0 then 1 else ⊤) else ENNReal.ofReal (cost / optimum)

theorem costRatio_le_iff (cost optimum K : ℝ)
    (hc : 0 ≤ cost) (ho : 0 ≤ optimum) (hK : 1 ≤ K) :
    costRatio cost optimum ≤ ENNReal.ofReal K ↔ cost ≤ K * optimum := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  by_cases hopt : optimum = 0
  · subst optimum
    by_cases hcost : cost = 0
    · subst cost
      have hk : (1 : ℝ≥0∞) ≤ ENNReal.ofReal K := by
        simpa using ENNReal.ofReal_le_ofReal hK
      simp [costRatio, hk]
    · have hcostpos : 0 < cost := lt_of_le_of_ne hc (Ne.symm hcost)
      simp [costRatio, hcost, not_le.mpr hcostpos]
  · have hoptpos : 0 < optimum := lt_of_le_of_ne ho (Ne.symm hopt)
    simp only [costRatio, if_neg hopt]
    rw [ENNReal.ofReal_le_ofReal_iff hK0, div_le_iff₀ hoptpos]

/-- Worst distortion over every stable lottery in every finite equally weighted election.
The extra supremum over reference candidates takes the minimum social cost in the denominator. -/
noncomputable def maximumDistortion (g : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (E : Election) (D : Lottery E.candidateCount) (_ : E.Stable g D)
    (d : E.Metric) (_ : E.Consistent d) (a : E.Candidate),
    costRatio (E.lotteryCost d D) (E.candidateCost d a)

/-- The zero-denominator-safe form of the universal upper bound. -/
def UniversalBound (g : ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ (E : Election) (D : Lottery E.candidateCount), E.Stable g D →
    ∀ d : E.Metric, E.Consistent d → ∀ a : E.Candidate,
      E.lotteryCost d D ≤ K * E.candidateCost d a

theorem maximumDistortion_le_iff (g : ℝ → ℝ) (K : ℝ) (hK : 1 ≤ K) :
    maximumDistortion g ≤ ENNReal.ofReal K ↔ UniversalBound g K := by
  simp only [maximumDistortion, iSup_le_iff, UniversalBound]
  apply forall_congr'
  intro E
  apply forall_congr'
  intro D
  apply forall_congr'
  intro _hstable
  apply forall_congr'
  intro d
  apply forall_congr'
  intro _hconsistent
  apply forall_congr'
  intro a
  exact costRatio_le_iff _ _ K (E.lotteryCost_nonneg d D) (E.candidateCost_nonneg d a) hK

/-- A concrete finite election witnessing a strict distortion lower bound. -/
def WitnessAbove (g : ℝ → ℝ) (K : ℝ) : Prop :=
  ∃ (E : Election) (D : Lottery E.candidateCount), E.Stable g D ∧
    ∃ d : E.Metric, E.Consistent d ∧ ∃ a : E.Candidate,
      0 < E.candidateCost d a ∧ K * E.candidateCost d a < E.lotteryCost d D

theorem witnessAbove_not_universalBound (g : ℝ → ℝ) (K : ℝ)
    (hw : WitnessAbove g K) : ¬ UniversalBound g K := by
  rintro hbound
  rcases hw with ⟨E, D, hstable, d, hconsistent, a, _hpos, hstrict⟩
  exact (not_lt_of_ge (hbound E D hstable d hconsistent a)) hstrict

theorem witnessAbove_mono (g : ℝ → ℝ) (K L : ℝ) (hLK : L ≤ K)
    (hw : WitnessAbove g K) : WitnessAbove g L := by
  rcases hw with ⟨E, D, hstable, d, hconsistent, a, hpos, hstrict⟩
  refine ⟨E, D, hstable, d, hconsistent, a, hpos, ?_⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hLK hpos.le) hstrict

end OptimalG
