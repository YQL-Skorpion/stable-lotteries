import OptimalG.UniversalLPIntegerCheck

/-! Optional checked expansion cache for the integer dual checker.
Normalization then reads an explicit literal list, avoiding repeated expansion
of array lookups while the kernel traverses the sparse terms. -/
namespace OptimalG.UniversalLP.IntegerDualCertificate

def checkWithExpansion (c : IntegerDualCertificate) (d : DualProposal) (rows : Array RowTag)
    (terms : Array Terms) (rhs : Array ℚ) (known : ℕ) (expansion : IntegerTerms) : Bool :=
  decide (0 < c.scale ∧ known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  decide (∀ i, d.multiplier i ≤ 0) &&
  scaledTermsCheck c.scale 1 d.objective c.objective &&
  decide (∀ i : Fin d.support.size,
    scaledTermsCheck c.scale (-d.multiplier i) terms[d.rowIndex i]!
      c.weightedRows[i.val]! = true) &&
  decide (normalizeIntegerTerms expansion = c.residual) &&
  decide (∀ j, scaledIntegerCheck c.scale (d.remainder j) (integerCoeff c.residual j) = true) &&
  decide (∀ i : Fin d.support.size,
    scaledProductCheck c.scale (d.multiplier i) (d.cachedRhs rhs i) c.rhsProducts[i.val]! = true) &&
  decide (∀ j : Variables,
    scaledProductCheck c.scale (d.remainder j) (lower j) c.lowerProducts[j.val]! = true ∧
    scaledProductCheck c.scale (d.remainder j) (upper j) c.upperProducts[j.val]! = true) &&
  scaledIntegerCheck c.scale d.bound c.bound &&
  decide (c.bound ≤ (∑ i : Fin d.support.size, c.rhsProducts[i.val]!) +
    ∑ j : Variables, min c.lowerProducts[j.val]! c.upperProducts[j.val]!)


def flatCheck (c : IntegerDualCertificate) (d : DualProposal) (rows : Array RowTag)
    (terms : Array Terms) (rhs : Array ℚ) (known : ℕ) (expansion : IntegerTerms) : Bool :=
  decide (c.expanded d = expansion) && c.checkWithExpansion d rows terms rhs known expansion

theorem checkCached_of_flatCheck {c : IntegerDualCertificate} {d : DualProposal}
    {rows : Array RowTag} {terms : Array Terms} {rhs : Array ℚ} {known : ℕ}
    {expansion : IntegerTerms} (hc : c.flatCheck d rows terms rhs known expansion = true) :
    d.checkCached rows terms rhs known = true := by
  have hh := Bool.and_eq_true_iff.mp hc
  have he : c.expanded d = expansion := of_decide_eq_true hh.1
  have hb := hh.2
  rw [← he] at hb
  exact checkCached_of_check hb

def checkWithCoefficients (c : IntegerDualCertificate) (d : DualProposal) (rows : Array RowTag)
    (terms : Array Terms) (rhs : Array ℚ) (known : ℕ) (expansion : IntegerTerms) : Bool :=
  decide (0 < c.scale ∧ known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  decide (∀ i, d.multiplier i ≤ 0) &&
  scaledTermsCheck c.scale 1 d.objective c.objective &&
  decide (∀ i : Fin d.support.size,
    scaledTermsCheck c.scale (-d.multiplier i) terms[d.rowIndex i]!
      c.weightedRows[i.val]! = true) &&
  decide (∀ j : Variables, integerCoeff expansion j = integerCoeff c.residual j) &&
  decide (∀ j, scaledIntegerCheck c.scale (d.remainder j) (integerCoeff c.residual j) = true) &&
  decide (∀ i : Fin d.support.size,
    scaledProductCheck c.scale (d.multiplier i) (d.cachedRhs rhs i) c.rhsProducts[i.val]! = true) &&
  decide (∀ j : Variables,
    scaledProductCheck c.scale (d.remainder j) (lower j) c.lowerProducts[j.val]! = true ∧
    scaledProductCheck c.scale (d.remainder j) (upper j) c.upperProducts[j.val]! = true) &&
  scaledIntegerCheck c.scale d.bound c.bound &&
  decide (c.bound ≤ (∑ i : Fin d.support.size, c.rhsProducts[i.val]!) +
    ∑ j : Variables, min c.lowerProducts[j.val]! c.upperProducts[j.val]!)


/-- An alternative that checks each of the fixed 402 integer coefficients
rather than sorting. The input is still an independently checked literal cache. -/
def flatCoeffCheck (c : IntegerDualCertificate) (d : DualProposal) (rows : Array RowTag)
    (terms : Array Terms) (rhs : Array ℚ) (known : ℕ) (expansion : IntegerTerms) : Bool :=
  decide (c.expanded d = expansion) && c.checkWithCoefficients d rows terms rhs known expansion

theorem checkCached_of_flatCoeffCheck {c : IntegerDualCertificate} {d : DualProposal}
    {rows : Array RowTag} {terms : Array Terms} {rhs : Array ℚ} {known : ℕ}
    {expansion : IntegerTerms} (hc : c.flatCoeffCheck d rows terms rhs known expansion = true) :
    d.checkCached rows terms rhs known = true := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hexp : c.expanded d = expansion := of_decide_eq_true hh.1
  have hc := hh.2
  simp only [checkWithCoefficients,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hidx,hsign⟩,hobj⟩,hrow⟩,hcoeff⟩,hres⟩,hrhs⟩,hbox⟩,hbound⟩,hsum⟩
  have hscale : (0 : ℚ) < c.scale := by exact_mod_cast hidx.1
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hidx.2,?_⟩
  apply decide_eq_true
  refine ⟨hsign,?_,?_⟩
  · intro j
    have he := coeff_expanded hobj hrow j
    rw [hexp,hcoeff j,scaledIntegerCheck_sound (hres j)] at he
    have he' := mul_left_cancel₀ (ne_of_gt hscale) he
    linarith
  · have he : (c.bound : ℚ) ≤ (∑ i : Fin d.support.size, (c.rhsProducts[i.val]! : ℚ)) +
        ∑ j : Variables, min (c.lowerProducts[j.val]! : ℚ) (c.upperProducts[j.val]! : ℚ) := by
      exact_mod_cast hsum
    rw [scaledIntegerCheck_sound hbound] at he
    simp_rw [scaledProductCheck_sound (hrhs _),
      scaledProductCheck_sound (hbox _).1,scaledProductCheck_sound (hbox _).2] at he
    simp_rw [mul_assoc,← mul_min_of_nonneg _ _ hscale.le] at he
    rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add] at he
    exact (mul_le_mul_iff_right₀ hscale).mp he

end OptimalG.UniversalLP.IntegerDualCertificate
