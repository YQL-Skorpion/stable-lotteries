import OptimalG.Certificates.TransportPushforward
import Mathlib.Tactic

/-! Ordered affine rank images form a partition apart from their finitely
many endpoints. Their density sum therefore selects exactly one summand;
two rank partitions can be overlaid without assuming a density formula. -/
namespace OptimalG.Variational
open Set MeasureTheory

noncomputable def rankPartitionDensity (n : ℕ) (node : ℕ → ℝ)
    (weight : ℕ → ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ i∈Finset.range n,if r∈Ioo (node i) (node (i+1)) then weight i r else 0

theorem rankPartition_cover {n : ℕ} {node : ℕ → ℝ} {r : ℝ}
    (hr : r∈Ioc (node 0) (node n)) :
    ∃ i<n,r∈Ioc (node i) (node (i+1)) := by
  induction n with
  | zero => exact False.elim (not_lt_of_ge hr.2 hr.1)
  | succ n ih =>
    by_cases hn : r≤node n
    · obtain ⟨i,hi,hri⟩ := ih ⟨hr.1,hn⟩
      exact ⟨i,by omega,hri⟩
    · exact ⟨n,by omega,lt_of_not_ge hn,hr.2⟩

theorem rankPartition_piece_unique {n i j : ℕ} {node : ℕ → ℝ} {r : ℝ}
    (hmono : MonotoneOn node (Icc 0 n)) (hi : i<n) (hj : j<n)
    (hri : r∈Ioo (node i) (node (i+1)))
    (hrj : r∈Ioo (node j) (node (j+1))) : i=j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · have hh := hmono (show i+1∈Icc 0 n by constructor <;> omega)
      (show j∈Icc 0 n by constructor <;> omega) (by omega : i+1≤j)
    linarith only [hh,hri.2,hrj.1]
  · have hh := hmono (show j+1∈Icc 0 n by constructor <;> omega)
      (show i∈Icc 0 n by constructor <;> omega) (by omega : j+1 ≤ i)
    linarith only [hh,hrj.2,hri.1]

theorem rankPartitionDensity_selected {n i : ℕ} {node : ℕ → ℝ} {r : ℝ}
    (hmono : MonotoneOn node (Icc 0 n)) (hi : i<n)
    (hri : r∈Ioo (node i) (node (i+1))) (weight : ℕ → ℝ → ℝ) :
    rankPartitionDensity n node weight r=weight i r := by
  classical
  unfold rankPartitionDensity
  rw [Finset.sum_eq_single i]
  · exact if_pos hri
  · intro j hj hji
    apply if_neg
    intro hrj
    exact hji (rankPartition_piece_unique hmono (Finset.mem_range.mp hj) hi hrj hri)
  · intro hi'
    exact False.elim (hi' (Finset.mem_range.mpr hi))

theorem rankPartitionDensity_ae_selected {n : ℕ} {node : ℕ → ℝ}
    (hmono : MonotoneOn node (Icc 0 n)) :
    ∀ᵐ r ∂volume.restrict (Icc (node 0) (node n)),∃ i<n,
      r∈Ioo (node i) (node (i+1)) ∧
      ∀ weight : ℕ → ℝ → ℝ,rankPartitionDensity n node weight r=weight i r := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae ((countable_range node).ae_notMem volume)] with r hr hnot
  have hr0 : node 0<r := lt_of_le_of_ne hr.1 (by
    intro he
    exact hnot ⟨0,he⟩)
  obtain ⟨i,hi,hri⟩ := rankPartition_cover ⟨hr0,hr.2⟩
  have htop : r<node (i+1) := lt_of_le_of_ne hri.2 (by
    intro he
    exact hnot ⟨i+1,he.symm⟩)
  exact ⟨i,hi,⟨hri.1,htop⟩,rankPartitionDensity_selected hmono hi ⟨hri.1,htop⟩⟩

theorem rankPartitionDensity_overlay_ae_bound {n m : ℕ} {node other : ℕ → ℝ}
    {weightR weightA : ℕ → ℝ → ℝ} {lower upper : ℝ}
    (hnode : MonotoneOn node (Icc 0 n)) (hother : MonotoneOn other (Icc 0 m))
    (hleft : node 0=other 0) (hright : node n=other m)
    (hbound : ∀ i<n,∀ j<m,∀ r∈Ioo (node i) (node (i+1))∩Ioo (other j) (other (j+1)),
      lower≤weightR i r+weightA j r ∧ weightR i r+weightA j r≤upper) :
    ∀ᵐ r ∂volume.restrict (Icc (node 0) (node n)),
      lower≤rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r ∧
      rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r≤upper := by
  have ha := rankPartitionDensity_ae_selected hother
  rw [←hleft,←hright] at ha
  filter_upwards [rankPartitionDensity_ae_selected hnode,ha] with r hr hs
  obtain ⟨i,hi,hri,heqi⟩ := hr
  obtain ⟨j,hj,hrj,heqj⟩ := hs
  rw [heqi weightR,heqj weightA]
  exact hbound i hi j hj r ⟨hri,hrj⟩

/-- A finite common refinement only has to check its two containing rank
cells. There is no quadratic search over every pair of original cells. -/
theorem rankPartitionDensity_refinement_ae_bound {n m k : ℕ}
    {node other fine : ℕ → ℝ} {selectR selectA : ℕ → ℕ}
    {weightR weightA : ℕ → ℝ → ℝ} {lower upper : ℝ}
    (hnode : MonotoneOn node (Icc 0 n)) (hother : MonotoneOn other (Icc 0 m))
    (hfine : MonotoneOn fine (Icc 0 k))
    (hselectR : ∀ i<k,selectR i<n ∧ node (selectR i)≤fine i ∧ fine (i+1)≤node (selectR i+1))
    (hselectA : ∀ i<k,selectA i<m ∧ other (selectA i)≤fine i ∧ fine (i+1)≤other (selectA i+1))
    (hbound : ∀ i<k,∀ r∈Ioo (fine i) (fine (i+1)),
      lower≤weightR (selectR i) r+weightA (selectA i) r ∧
      weightR (selectR i) r+weightA (selectA i) r≤upper) :
    ∀ᵐ r ∂volume.restrict (Icc (fine 0) (fine k)),
      lower≤rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r ∧
      rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r≤upper := by
  filter_upwards [rankPartitionDensity_ae_selected hfine] with r hr
  obtain ⟨i,hi,hri,_⟩ := hr
  have hR := hselectR i hi
  have hA := hselectA i hi
  rw [rankPartitionDensity_selected hnode hR.1
    ⟨hR.2.1.trans_lt hri.1,hri.2.trans_le hR.2.2⟩ weightR,
    rankPartitionDensity_selected hother hA.1
    ⟨hA.2.1.trans_lt hri.1,hri.2.trans_le hA.2.2⟩ weightA]
  exact hbound i hi r hri

theorem rankPartitionDensity_zero_outside {n : ℕ} {node : ℕ → ℝ} {r : ℝ}
    (hmono : MonotoneOn node (Icc 0 n))
    (hr : r≤node 0 ∨ node n≤r) (weight : ℕ → ℝ → ℝ) :
    rankPartitionDensity n node weight r=0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  have hin : i<n := Finset.mem_range.mp hi
  apply if_neg
  intro hri
  rcases hr with hleft | hright
  · have hn := hmono (show 0∈Icc 0 n by constructor <;> omega)
      (show i∈Icc 0 n by constructor <;> omega) (Nat.zero_le i)
    linarith only [hn,hleft,hri.1]
  · have hn := hmono (show i+1∈Icc 0 n by constructor <;> omega)
      (show n∈Icc 0 n by constructor <;> omega) (by omega : i+1≤n)
    linarith only [hn,hright,hri.2]

/-- One rank image may end before the other. A missing second contributor
is certified by the fine cell lying entirely outside its rank support. -/
theorem rankPartitionDensity_optional_refinement_ae_bound {n m k : ℕ}
    {node other fine : ℕ → ℝ} {selectR : ℕ → ℕ} {selectA : ℕ → Option ℕ}
    {weightR weightA : ℕ → ℝ → ℝ} {lower upper : ℝ}
    (hnode : MonotoneOn node (Icc 0 n)) (hother : MonotoneOn other (Icc 0 m))
    (hfine : MonotoneOn fine (Icc 0 k))
    (hselectR : ∀ i<k,selectR i<n ∧ node (selectR i)≤fine i ∧ fine (i+1)≤node (selectR i+1))
    (hselectA : ∀ i<k,match selectA i with
      | none => fine (i+1)≤other 0 ∨ other m≤fine i
      | some j => j<m ∧ other j≤fine i ∧ fine (i+1)≤other (j+1))
    (hbound : ∀ i<k,∀ r∈Ioo (fine i) (fine (i+1)),
      lower≤weightR (selectR i) r+(selectA i).elim 0 (fun j=>weightA j r) ∧
      weightR (selectR i) r+(selectA i).elim 0 (fun j=>weightA j r)≤upper) :
    ∀ᵐ r ∂volume.restrict (Icc (fine 0) (fine k)),
      lower≤rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r ∧
      rankPartitionDensity n node weightR r+rankPartitionDensity m other weightA r≤upper := by
  filter_upwards [rankPartitionDensity_ae_selected hfine] with r hr
  obtain ⟨i,hi,hri,_⟩ := hr
  have hR := hselectR i hi
  rw [rankPartitionDensity_selected hnode hR.1
    ⟨hR.2.1.trans_lt hri.1,hri.2.trans_le hR.2.2⟩ weightR]
  have hA := hselectA i hi
  have hB := hbound i hi r hri
  cases hsel : selectA i with
  | none =>
    simp only [hsel] at hA hB
    have hout : r≤other 0 ∨ other m≤r := by
      rcases hA with hl | hr
      · exact Or.inl (hri.2.le.trans hl)
      · exact Or.inr (hr.trans hri.1.le)
    rw [rankPartitionDensity_zero_outside hother hout weightA]
    simpa only [Option.elim_none] using hB
  | some j =>
    simp only [hsel] at hA hB
    rw [rankPartitionDensity_selected hother hA.1
      ⟨hA.2.1.trans_lt hri.1,hri.2.trans_le hA.2.2⟩ weightA]
    simpa only [Option.elim_some] using hB

end OptimalG.Variational
