import OptimalG.Certificates.StaticLayerCover

/-! Bounded adjacency certificates compose without rechecking their cells. -/
namespace OptimalG.Certificates.StaticSupport

theorem continuousCellCoverCheck_append {a b c : ℚ}
    {xs ys : List ContinuousLayerCell}
    (hx : continuousCellCoverCheck a b xs=true)
    (hy : continuousCellCoverCheck b c ys=true) :
    continuousCellCoverCheck a c (xs++ys)=true := by
  induction xs generalizing a with
  | nil =>
      have hab : a=b := of_decide_eq_true hx
      subst a
      simpa only [List.nil_append] using hy
  | cons x xs ih =>
      change (decide (x.lo=a ∧ x.lo<x.hi) && continuousCellCoverCheck x.hi b xs)=true at hx
      change (decide (x.lo=a ∧ x.lo<x.hi) && continuousCellCoverCheck x.hi c (xs++ys))=true
      rw [Bool.and_eq_true_iff] at hx ⊢
      exact ⟨hx.1,ih hx.2⟩

end OptimalG.Certificates.StaticSupport
