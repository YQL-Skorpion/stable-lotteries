import OptimalG.UniversalLPEncoding

/-! Sparse row references and proposed residuals for rational dual checking. -/
namespace OptimalG.UniversalLP

structure DualProposal where
  support : Array (ℕ × ℚ)
  objective : Terms
  residual : Array ℚ
  bound : ℚ
  deriving Inhabited

namespace DualProposal

def rowIndex (d : DualProposal) (i : Fin d.support.size) : ℕ := (d.support[i]).1
def multiplier (d : DualProposal) (i : Fin d.support.size) : ℚ := (d.support[i]).2
def matrix (d : DualProposal) (rows : Array RowTag) (i : Fin d.support.size) : Variables → ℚ :=
  rowCoeff (rows[d.rowIndex i]!)
def rhs (d : DualProposal) (rows : Array RowTag) (i : Fin d.support.size) : ℚ :=
  rowRhs (rows[d.rowIndex i]!)
def remainder (d : DualProposal) (j : Variables) : ℚ := d.residual[j.val]!

def check (d : DualProposal) (rows : Array RowTag) (known : ℕ) : Bool :=
  decide (known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  checkRationalDual (d.matrix rows) (d.rhs rows) d.multiplier
    (coeff d.objective) d.remainder lower upper d.bound

theorem check_sound {d : DualProposal} {rows : Array RowTag} {known : ℕ}
    (hc : d.check rows known = true) (w : Variables → ℝ)
    (hknown : ∀ i < known, RowHolds rows[i]! w)
    (hlo : ∀ j, (lower j : ℝ) ≤ w j) (hhi : ∀ j, w j ≤ upper j) :
    (d.bound : ℝ) ≤ ∑ j, (coeff d.objective j : ℝ) * w j := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hidx : known ≤ rows.size ∧ ∀ i, d.rowIndex i < known := of_decide_eq_true hh.1
  exact checkRationalDual_sound (d.matrix rows) (d.rhs rows) d.multiplier
    (coeff d.objective) d.remainder lower upper d.bound hh.2 w
    (fun i => hknown (d.rowIndex i) (hidx.2 i)) hlo hhi

/-- The cache is checked separately once, avoiding repeated rational row
reconstruction in every coefficient of every dual certificate. -/
def checkRowCache (rows : Array RowTag) (terms : Array Terms) (rhs : Array ℚ) : Bool :=
  decide (∀ i : Fin rows.size, terms[i.val]! = rowTerms rows[i.val]! ∧ rhs[i.val]! = rowRhs rows[i.val]!)

def cachedMatrix (d : DualProposal) (terms : Array Terms) (i : Fin d.support.size) : Variables → ℚ :=
  coeff (terms[d.rowIndex i]!)

def cachedRhs (d : DualProposal) (rhs : Array ℚ) (i : Fin d.support.size) : ℚ := rhs[d.rowIndex i]!

def checkCached (d : DualProposal) (rows : Array RowTag) (terms : Array Terms) (rhs : Array ℚ)
    (known : ℕ) : Bool :=
  decide (known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  checkRationalDual (d.cachedMatrix terms) (d.cachedRhs rhs) d.multiplier
    (coeff d.objective) d.remainder lower upper d.bound

theorem checkCached_sound {d : DualProposal} {rows : Array RowTag}
    {terms : Array Terms} {rhs : Array ℚ} {known : ℕ}
    (hcache : checkRowCache rows terms rhs = true)
    (hc : d.checkCached rows terms rhs known = true) (w : Variables → ℝ)
    (hknown : ∀ i < known, RowHolds rows[i]! w)
    (hlo : ∀ j, (lower j : ℝ) ≤ w j) (hhi : ∀ j, w j ≤ upper j) :
    (d.bound : ℝ) ≤ ∑ j, (coeff d.objective j : ℝ) * w j := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hidx : known ≤ rows.size ∧ ∀ i, d.rowIndex i < known := of_decide_eq_true hh.1
  have ht : ∀ i : Fin rows.size, terms[i.val]! = rowTerms rows[i.val]! ∧ rhs[i.val]! = rowRhs rows[i.val]! :=
    of_decide_eq_true hcache
  apply checkRationalDual_sound (d.cachedMatrix terms) (d.cachedRhs rhs) d.multiplier
    (coeff d.objective) d.remainder lower upper d.bound hh.2 w _ hlo hhi
  intro i
  have hi : d.rowIndex i < rows.size := (hidx.2 i).trans_le hidx.1
  have hrow := hknown (d.rowIndex i) (hidx.2 i)
  have hcached := ht ⟨d.rowIndex i, hi⟩
  change ∑ j, (coeff terms[d.rowIndex i]! j : ℝ) * w j ≤ rhs[d.rowIndex i]!
  rw [hcached.1, hcached.2]
  exact hrow

end DualProposal
end OptimalG.UniversalLP
