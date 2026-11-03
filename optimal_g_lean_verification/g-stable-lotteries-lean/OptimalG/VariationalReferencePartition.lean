import OptimalG.VariationalPartitionDensity
import Mathlib.Algebra.BigOperators.Fin

/-! The partition-density selection theorem applies to the actual finite
reference-segment definition, retaining its inverse affine maps and slopes. -/
namespace OptimalG.Variational
open Set MeasureTheory Certificates.Transport

theorem referenceSegments_ofFn (n : ℕ) (node : ℕ → ReferenceNode) :
    referenceSegments (List.ofFn (fun i : Fin (n+1) => node i)) =
      List.ofFn (fun i : Fin n => (⟨node i,node (i+1)⟩ : ReferenceSegment)) := by
  induction n generalizing node with
  | zero => simp [List.ofFn_succ,referenceSegments]
  | succ n ih =>
    simpa only [List.ofFn_succ,Fin.val_cast,Fin.val_zero,Fin.val_succ,referenceSegments,
      Nat.zero_add,Nat.add_assoc] using
      congrArg (List.cons (⟨node 0,node 1⟩ : ReferenceSegment)) (ih (fun i => node (i+1)))

theorem pushforwardDensity_ofFn_eq_rankPartitionDensity {n : ℕ}
    (segment : ℕ → ReferenceSegment) (rank : ReferenceNode → ℚ)
    (node : ℕ → ℝ) (weight : ReferenceSegment → ℝ → ℝ)
    (hleft : ∀ i<n,(rank (segment i).left:ℝ)=node i)
    (hright : ∀ i<n,(rank (segment i).right:ℝ)=node (i+1)) (r : ℝ) :
    pushforwardDensity (List.ofFn (fun i : Fin n => segment i)) rank weight r =
      rankPartitionDensity n node
        (fun i r => weight (segment i) ((segment i).inverseRankMap rank r)/
          ((segment i).slope rank:ℝ)) r := by
  classical
  unfold pushforwardDensity rankPartitionDensity
  rw [List.map_ofFn,List.sum_ofFn,Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  unfold segmentDensity
  dsimp only [Function.comp_apply]
  rw [hleft i i.isLt,hright i i.isLt]

theorem pushforwardDensity_referenceSegments_eq_rankPartitionDensity (n : ℕ)
    (node : ℕ → ReferenceNode) (rank : ReferenceNode → ℚ)
    (weight : ReferenceSegment → ℝ → ℝ) (r : ℝ) :
    pushforwardDensity (referenceSegments (List.ofFn (fun i : Fin (n+1) => node i))) rank weight r =
      rankPartitionDensity n (fun i => (rank (node i):ℝ))
        (fun i r => weight ⟨node i,node (i+1)⟩
          ((⟨node i,node (i+1)⟩ : ReferenceSegment).inverseRankMap rank r)/
          ((⟨node i,node (i+1)⟩ : ReferenceSegment).slope rank:ℝ)) r := by
  rw [referenceSegments_ofFn]
  exact pushforwardDensity_ofFn_eq_rankPartitionDensity
    (fun i => ⟨node i,node (i+1)⟩) rank (fun i => (rank (node i):ℝ)) weight
    (fun _ _ => rfl) (fun _ _ => rfl) r

end OptimalG.Variational
