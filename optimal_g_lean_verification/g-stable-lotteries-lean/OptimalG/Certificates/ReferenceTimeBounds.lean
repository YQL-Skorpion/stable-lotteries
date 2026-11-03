import OptimalG.Certificates.ReferenceScalarExpressions
import OptimalG.Certificates.IntegerEnclosures

/-! The three time/warp coordinates of a frozen Hessian box are checked
against the actual affine time map and its scalar-parameter warp. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set RatExpr

def timeBoundsCheck (s k : ℕ) (c : ReferenceScalarCell)
    (time warp slope : IntegerInterval) : Bool :=
  c.flow.highRank.enclosureRefinedCheck s k (fun _=>⟨0,s⟩) time &&
    (c.warp.enclosureRefinedCheck s k (fun _=>⟨0,s⟩) warp &&
     c.warpDerivative.enclosureRefinedCheck s k (fun _=>⟨0,s⟩) slope)

theorem checked_time_bounds {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (time warp slope : IntegerInterval)
    (hc : c.timeBoundsCheck s k time warp slope=true)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    time.Contains s (c.frozenInput t 5) ∧
    warp.Contains s (c.frozenInput t 6) ∧
    slope.Contains s (c.frozenInput t 11) := by
  obtain ⟨htc,hrest⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hwc,hsc⟩ := Bool.and_eq_true_iff.mp hrest
  have hu : ∀ j : Fin 1,(⟨0,(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro j
    exact ⟨by simpa using mul_nonneg (Nat.cast_nonneg s) ht.1,
      by simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)⟩
  have ht' := RatExpr.enclosureRefinedCheck_sound hs hk c.flow.highRank
    (fun _=>⟨0,s⟩) time htc (fun _=>t) hu
  have hw' := RatExpr.enclosureRefinedCheck_sound hs hk c.warp
    (fun _=>⟨0,s⟩) warp hwc (fun _=>t) hu
  have hs' := RatExpr.enclosureRefinedCheck_sound hs hk c.warpDerivative
    (fun _=>⟨0,s⟩) slope hsc (fun _=>t) hu
  simpa [frozenInput,frozenSubstitution,Matrix.cons_val_zero,Matrix.cons_val_succ,
    RatExpr.evalOne] using And.intro ht' (And.intro hw' hs')

end OptimalG.Certificates.Transport.ReferenceScalarCell
