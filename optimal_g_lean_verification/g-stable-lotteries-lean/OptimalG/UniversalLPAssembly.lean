import OptimalG.UniversalLPStages

/-! # Sequential semantics of the universal LP certificate

Strong induction permits a moving-row ratio certificate to use only basic rows
or earlier moving rows. Its two objective identities and high-bin width are
checked explicitly by `MovingStage.Valid`.
-/
namespace OptimalG.UniversalLP

/-- All rows in a checked sequential prefix hold for actual primitive data. -/
theorem sequential_rows {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions (L : ℝ) phi)
    (rows : Array RowTag) (terms : Array Terms) (rhs : Array ℚ)
    (base : ℕ) (stages : Array MovingStage)
    (hcache : DualProposal.checkRowCache rows terms rhs = true)
    (hbase : ∀ i < base, BaseRowValid rows[i]!)
    (htag : ∀ s < stages.size, rows[base + s]! = stages[s]!.tag)
    (hvalid : ∀ s < stages.size, stages[s]!.Valid)
    (hx : ∀ s < stages.size, stages[s]!.xDual.checkCached rows terms rhs (base + s) = true)
    (hy : ∀ s < stages.size, stages[s]!.yDual.checkCached rows terms rhs (base + s) = true) :
    ∀ i < base + stages.size, RowHolds rows[i]! (gridValues phi) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi
    by_cases hib : i < base
    · exact BaseRowValid.sound h.toNormalizedNecessaryTwoClass (hbase i hib)
    · have hs : i - base < stages.size := by omega
      have heq : base + (i - base) = i := by omega
      have hknown : ∀ j < base + (i - base), RowHolds rows[j]! (gridValues phi) := by
        intro j hj
        exact ih j (by omega) (by omega)
      have hh := MovingStage.sound h stages[i - base]! (hvalid (i - base) hs)
        hcache (hx (i - base) hs) (hy (i - base) hs) hknown
      rw [← htag (i - base) hs, heq] at hh
      exact hh

/-- A final checked objective bound, with every row discharged by the actual
election inequalities and the preceding sequential ratio certificates. -/
theorem sequential_objective_bound {phi : ℝ → ℝ} (h : NormalizedNecessaryConditions (L : ℝ) phi)
    (rows : Array RowTag) (terms : Array Terms) (rhs : Array ℚ)
    (base : ℕ) (stages : Array MovingStage)
    (hcache : DualProposal.checkRowCache rows terms rhs = true)
    (hbase : ∀ i < base, BaseRowValid rows[i]!)
    (htag : ∀ s < stages.size, rows[base + s]! = stages[s]!.tag)
    (hvalid : ∀ s < stages.size, stages[s]!.Valid)
    (hx : ∀ s < stages.size, stages[s]!.xDual.checkCached rows terms rhs (base + s) = true)
    (hy : ∀ s < stages.size, stages[s]!.yDual.checkCached rows terms rhs (base + s) = true)
    (d : DualProposal) (hd : d.checkCached rows terms rhs (base + stages.size) = true) :
    (d.bound : ℝ) ≤ termsValue (gridValues phi) d.objective := by
  have hh := DualProposal.checkCached_sound hcache hd (gridValues phi)
    (sequential_rows h rows terms rhs base stages hcache hbase htag hvalid hx hy)
    (gridValues_lower h.toNormalizedNecessaryTwoClass) (gridValues_upper h.toNormalizedNecessaryTwoClass)
  rwa [coeff_value] at hh

end OptimalG.UniversalLP
