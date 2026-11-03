import OptimalG.VariationalPartitionDensity

/-! A finite Boolean geometry check supplies the actual monotonicity and
containment premises of the cropped, optional-contributor rank overlay. -/
namespace OptimalG.Certificates.Transport
open Set

def weakRankOrderCheck : List ℚ → Bool
  | [] => true
  | [_] => true
  | a::b::xs => decide (a≤b) && weakRankOrderCheck (b::xs)

theorem weakRankOrderCheck_adjacent {xs : List ℚ} (hc : weakRankOrderCheck xs=true)
    {i : ℕ} (hi : i+1<xs.length) : xs[i]?.getD 0≤xs[i+1]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases xs with
    | nil => simp at hi
    | cons b bs =>
      have hh := Bool.and_eq_true_iff.mp hc
      cases i with
      | zero => simpa using (of_decide_eq_true hh.1 : a≤b)
      | succ i =>
        have hh' := ih hh.2 (i:=i) (by simp only [List.length_cons] at hi ⊢; omega)
        simpa only [List.getElem?_cons_succ,Nat.succ_eq_add_one,Nat.add_assoc] using hh'

theorem weakRankOrderCheck_monotone {xs : List ℚ} {n : ℕ}
    (hc : weakRankOrderCheck xs=true) (hlen : xs.length=n+1) :
    MonotoneOn (fun i : ℕ => (xs[i]?.getD 0:ℝ)) (Icc 0 n) := by
  have hh : ∀ j,j≤n → ∀ i,i≤j → xs[i]?.getD 0≤xs[j]?.getD 0 := by
    intro j
    induction j with
    | zero =>
      intro _ i hi
      have he : i=0 := Nat.eq_zero_of_le_zero hi
      subst i
      exact le_rfl
    | succ j ih =>
      intro hj i hi
      by_cases hij : i≤j
      · exact (ih (by omega) i hij).trans
          (weakRankOrderCheck_adjacent hc (by rw [hlen]; omega))
      · have he : i=j+1 := by omega
        subst i
        exact le_rfl
  intro i hi j hj hij
  dsimp only
  exact_mod_cast hh j hj.2 i hij

structure RankOverlayArrays where
  nodeR : List ℚ
  nodeA : List ℚ
  fine : List ℚ
  selectR : List ℕ
  selectA : List (Option ℕ)
  deriving Repr, DecidableEq

namespace RankOverlayArrays

def rCount (d : RankOverlayArrays) : ℕ := d.nodeR.length-1
def aCount (d : RankOverlayArrays) : ℕ := d.nodeA.length-1
def cellCount (d : RankOverlayArrays) : ℕ := d.selectR.length
noncomputable def rNode (d : RankOverlayArrays) (i : ℕ) : ℝ := (d.nodeR[i]?.getD 0:ℝ)
noncomputable def aNode (d : RankOverlayArrays) (i : ℕ) : ℝ := (d.nodeA[i]?.getD 0:ℝ)
noncomputable def fineNode (d : RankOverlayArrays) (i : ℕ) : ℝ := (d.fine[i]?.getD 0:ℝ)
def rIndex (d : RankOverlayArrays) (i : ℕ) : ℕ := d.selectR[i]?.getD 0
def aIndex (d : RankOverlayArrays) (i : ℕ) : Option ℕ := d.selectA[i]?.getD none

def cellGeometryCheck (d : RankOverlayArrays) (i : ℕ) : Bool :=
  decide (d.rIndex i<d.rCount ∧
    d.nodeR[d.rIndex i]?.getD 0≤d.fine[i]?.getD 0 ∧
    d.fine[i+1]?.getD 0≤d.nodeR[d.rIndex i+1]?.getD 0) &&
    (match d.aIndex i with
    | none => decide (d.fine[i+1]?.getD 0≤d.nodeA[0]?.getD 0 ∨
        d.nodeA[d.aCount]?.getD 0≤d.fine[i]?.getD 0)
    | some j => decide (j<d.aCount ∧ d.nodeA[j]?.getD 0≤d.fine[i]?.getD 0 ∧
        d.fine[i+1]?.getD 0≤d.nodeA[j+1]?.getD 0))

def geometryCheck (d : RankOverlayArrays) : Bool :=
  decide (0<d.nodeR.length ∧ 0<d.nodeA.length ∧
    d.fine.length=d.cellCount+1 ∧ d.selectA.length=d.cellCount) &&
  (weakRankOrderCheck d.nodeR && (weakRankOrderCheck d.nodeA &&
    (weakRankOrderCheck d.fine && (List.range d.cellCount).all d.cellGeometryCheck)))

/-- Per-cell proofs can be checked in bounded data chunks and assembled
without reevaluating all selector lookups in one reduction. -/
theorem geometryCheck_of_parts {d : RankOverlayArrays}
    (hsize : 0<d.nodeR.length ∧ 0<d.nodeA.length ∧
      d.fine.length=d.cellCount+1 ∧ d.selectA.length=d.cellCount)
    (hR : weakRankOrderCheck d.nodeR=true) (hA : weakRankOrderCheck d.nodeA=true)
    (hF : weakRankOrderCheck d.fine=true)
    (hcells : ∀ i<d.cellCount,d.cellGeometryCheck i=true) : d.geometryCheck=true := by
  simp only [geometryCheck,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨hsize,hR,hA,hF,List.all_eq_true.mpr (fun i hi=>hcells i (List.mem_range.mp hi))⟩

theorem geometryCheck_sound {d : RankOverlayArrays} (hc : d.geometryCheck=true) :
    MonotoneOn d.rNode (Icc 0 d.rCount) ∧
    MonotoneOn d.aNode (Icc 0 d.aCount) ∧
    MonotoneOn d.fineNode (Icc 0 d.cellCount) ∧
    (∀ i<d.cellCount,d.rIndex i<d.rCount ∧ d.rNode (d.rIndex i)≤d.fineNode i ∧
      d.fineNode (i+1)≤d.rNode (d.rIndex i+1)) ∧
    (∀ i<d.cellCount,match d.aIndex i with
      | none => d.fineNode (i+1)≤d.aNode 0 ∨ d.aNode d.aCount≤d.fineNode i
      | some j => j<d.aCount ∧ d.aNode j≤d.fineNode i ∧ d.fineNode (i+1)≤d.aNode (j+1)) := by
  simp only [geometryCheck,Bool.and_eq_true] at hc
  have hsize : 0<d.nodeR.length ∧ 0<d.nodeA.length ∧
      d.fine.length=d.cellCount+1 ∧ d.selectA.length=d.cellCount := of_decide_eq_true hc.1
  have hRlen : d.nodeR.length=d.rCount+1 := by dsimp only [rCount]; omega
  have hAlen : d.nodeA.length=d.aCount+1 := by dsimp only [aCount]; omega
  refine ⟨weakRankOrderCheck_monotone hc.2.1 hRlen,
    weakRankOrderCheck_monotone hc.2.2.1 hAlen,
    weakRankOrderCheck_monotone hc.2.2.2.1 hsize.2.2.1,?_,?_⟩
  · intro i hi
    have hi' := List.all_eq_true.mp hc.2.2.2.2 i (List.mem_range.mpr hi)
    have hh := of_decide_eq_true (Bool.and_eq_true_iff.mp hi').1
    refine ⟨hh.1,?_,?_⟩
    · dsimp only [rNode,fineNode]; exact_mod_cast hh.2.1
    · dsimp only [rNode,fineNode]; exact_mod_cast hh.2.2
  · intro i hi
    have hi' := List.all_eq_true.mp hc.2.2.2.2 i (List.mem_range.mpr hi)
    have hh := (Bool.and_eq_true_iff.mp hi').2
    cases he : d.aIndex i with
    | none =>
      simp only [he] at hh ⊢
      rcases of_decide_eq_true hh with hl | hr
      · exact Or.inl (by dsimp only [fineNode,aNode]; exact_mod_cast hl)
      · exact Or.inr (by dsimp only [fineNode,aNode]; exact_mod_cast hr)
    | some j =>
      simp only [he] at hh ⊢
      have hh' := of_decide_eq_true hh
      exact ⟨hh'.1,by dsimp only [fineNode,aNode]; exact_mod_cast hh'.2.1,
        by dsimp only [fineNode,aNode]; exact_mod_cast hh'.2.2⟩

theorem geometryCheck_overlay_bound {d : RankOverlayArrays} (hc : d.geometryCheck=true)
    {weightR weightA : ℕ → ℝ → ℝ} {lower upper : ℝ}
    (hbound : ∀ i<d.cellCount,∀ r∈Ioo (d.fineNode i) (d.fineNode (i+1)),
      lower≤weightR (d.rIndex i) r+(d.aIndex i).elim 0 (fun j=>weightA j r) ∧
      weightR (d.rIndex i) r+(d.aIndex i).elim 0 (fun j=>weightA j r)≤upper) :
    ∀ᵐ r ∂MeasureTheory.volume.restrict (Icc (d.fineNode 0) (d.fineNode d.cellCount)),
      lower≤Variational.rankPartitionDensity d.rCount d.rNode weightR r+
        Variational.rankPartitionDensity d.aCount d.aNode weightA r ∧
      Variational.rankPartitionDensity d.rCount d.rNode weightR r+
        Variational.rankPartitionDensity d.aCount d.aNode weightA r≤upper := by
  have hh := geometryCheck_sound hc
  exact Variational.rankPartitionDensity_optional_refinement_ae_bound
    hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2 hbound

theorem geometryCheck_selected {d : RankOverlayArrays} (hc : d.geometryCheck=true)
    {i : ℕ} (hi : i<d.cellCount) {r : ℝ}
    (hr : r∈Ioo (d.fineNode i) (d.fineNode (i+1)))
    (weightR weightA : ℕ → ℝ → ℝ) :
    Variational.rankPartitionDensity d.rCount d.rNode weightR r+
        Variational.rankPartitionDensity d.aCount d.aNode weightA r=
      weightR (d.rIndex i) r+(d.aIndex i).elim 0 (fun j=>weightA j r) := by
  have hh := geometryCheck_sound hc
  have hR := hh.2.2.2.1 i hi
  rw [Variational.rankPartitionDensity_selected hh.1 hR.1
    ⟨hR.2.1.trans_lt hr.1,hr.2.trans_le hR.2.2⟩ weightR]
  have hA := hh.2.2.2.2 i hi
  cases hsel : d.aIndex i with
  | none =>
    simp only [hsel] at hA
    have hout : r≤d.aNode 0 ∨ d.aNode d.aCount≤r := by
      rcases hA with hl | hu
      · exact Or.inl (hr.2.le.trans hl)
      · exact Or.inr (hu.trans hr.1.le)
    rw [Variational.rankPartitionDensity_zero_outside hh.2.1 hout weightA]
    rfl
  | some j =>
    simp only [hsel] at hA
    rw [Variational.rankPartitionDensity_selected hh.2.1 hA.1
      ⟨hA.2.1.trans_lt hr.1,hr.2.trans_le hA.2.2⟩ weightA]
    rfl

end RankOverlayArrays
end OptimalG.Certificates.Transport
