import OptimalG.Certificates.Expression

/-! Exact indexed coverage for independently checked polynomial leaves.
Coverage is proved by real case splits along the declared rational cuts. -/
namespace OptimalG.Certificates

inductive IndexedBoxCover (n k : ℕ) where
  | leaf : Fin k → IndexedBoxCover n k
  | split : Fin n → ℚ → IndexedBoxCover n k → IndexedBoxCover n k → IndexedBoxCover n k
  deriving DecidableEq, Repr

namespace IndexedBoxCover
variable {n k : ℕ}
open BoxCertificate

def check (leaves : Fin k→Fin n→RatInterval) (box : Fin n→RatInterval) : IndexedBoxCover n k→Bool
  | .leaf j => decide (∀ i,box i=leaves j i)
  | .split i m left right => check leaves (leftBox box i m) left && check leaves (rightBox box i m) right

theorem covers (t : IndexedBoxCover n k) (leaves : Fin k→Fin n→RatInterval) :
    ∀ box,check leaves box t=true→∀ x : Fin n→ℝ,
      (∀ i,(box i).Contains (x i))→∃ j,∀ i,(leaves j i).Contains (x i) := by
  induction t with
  | leaf j =>
    intro box hc x hx
    have he : ∀ i,box i=leaves j i := of_decide_eq_true hc
    exact ⟨j,fun i=>by rw [←he i];exact hx i⟩
  | split i m left right ihl ihr =>
    intro box hc x hx
    have hh : check leaves (leftBox box i m) left=true ∧
        check leaves (rightBox box i m) right=true := by
      simpa only [check,Bool.and_eq_true_iff] using hc
    by_cases hm : x i≤(m:ℝ)
    · apply ihl (leftBox box i m) hh.1 x
      intro j
      by_cases hji : j=i
      · subst j
        simpa [leftBox,RatInterval.Contains] using And.intro (hx i).1 hm
      · simpa [leftBox,Function.update_of_ne hji] using hx j
    · apply ihr (rightBox box i m) hh.2 x
      intro j
      by_cases hji : j=i
      · subst j
        simpa [rightBox,RatInterval.Contains] using And.intro (le_of_not_ge hm) (hx i).2
      · simpa [rightBox,Function.update_of_ne hji] using hx j

end IndexedBoxCover
end OptimalG.Certificates
