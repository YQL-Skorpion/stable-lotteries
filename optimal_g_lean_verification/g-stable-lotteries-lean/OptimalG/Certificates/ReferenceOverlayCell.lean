import OptimalG.Certificates.ReferenceDensityCell

/-! A fine rank cell combines the actual one or two selected affine density
components. Absent contributions are represented by an empty list, not by a
fictitious control segment. -/
namespace OptimalG.Certificates
open Set
namespace IntegerInterval

def sumRounded : List IntegerInterval→IntegerInterval
  | [] => ⟨0,0⟩
  | b::bs => b.addRounded (sumRounded bs)

theorem sumRounded_contains {α : Type*} {s : ℕ} (xs : List α)
    (bounds : α→IntegerInterval) (value : α→ℝ)
    (hx : ∀ x∈xs,(bounds x).Contains s (value x)) :
    (sumRounded (xs.map bounds)).Contains s ((xs.map value).sum) := by
  induction xs with
  | nil => simp [sumRounded,Contains]
  | cons a xs ih =>
    simpa only [List.map_cons,List.sum_cons,sumRounded] using
      addRounded_contains (hx a List.mem_cons_self)
        (ih (fun x h => hx x (List.mem_cons_of_mem a h)))

end IntegerInterval
namespace Transport

structure ReferenceOverlayCell where
  lo : ℚ
  hi : ℚ
  components : List ReferenceDensityCell
  position : IntegerInterval
  weight : IntegerInterval

namespace ReferenceOverlayCell

def imageCheck (c : ReferenceOverlayCell) (d : ReferenceDensityCell) : Bool :=
  decide (d.rank d.segment.left≤c.lo ∧ c.hi≤d.rank d.segment.right)

def check (c : ReferenceOverlayCell) : Bool :=
  decide (c.lo<c.hi) && c.components.all c.imageCheck &&
    (IntegerInterval.sumRounded (c.components.map (·.mappedPosition))).subsetCheck c.position &&
    (IntegerInterval.sumRounded (c.components.map (·.mappedWeight))).subsetCheck c.weight

theorem checked_images (c : ReferenceOverlayCell) (hc : c.check=true)
    {d : ReferenceDensityCell} (hd : d∈c.components) {r : ℝ}
    (hr : r∈Ioo (c.lo:ℝ) c.hi) :
    r∈Ioo (d.rank d.segment.left:ℝ) (d.rank d.segment.right:ℝ) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  have hg : d.rank d.segment.left≤c.lo ∧ c.hi≤d.rank d.segment.right :=
    of_decide_eq_true (List.all_eq_true.mp hh.1.1.2 d hd)
  exact ⟨(show (d.rank d.segment.left:ℝ)≤c.lo by exact_mod_cast hg.1).trans_lt hr.1,
    hr.2.trans_le (by exact_mod_cast hg.2)⟩

theorem checked_sums {s : ℕ} (c : ReferenceOverlayCell) (hc : c.check=true)
    (position weight : ReferenceDensityCell→ℝ)
    (hp : ∀ d∈c.components,d.mappedPosition.Contains s (position d))
    (hw : ∀ d∈c.components,d.mappedWeight.Contains s (weight d)) :
    c.position.Contains s ((c.components.map position).sum) ∧
    c.weight.Contains s ((c.components.map weight).sum) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  exact ⟨IntegerInterval.subsetCheck_sound
      (IntegerInterval.sumRounded_contains c.components (·.mappedPosition) position hp) hh.1.2,
    IntegerInterval.subsetCheck_sound
      (IntegerInterval.sumRounded_contains c.components (·.mappedWeight) weight hw) hh.2⟩

end ReferenceOverlayCell
end Transport
end OptimalG.Certificates
