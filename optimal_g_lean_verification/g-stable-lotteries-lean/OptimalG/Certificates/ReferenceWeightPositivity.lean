import OptimalG.Certificates.ReferenceWeightCell

/-! Positive actual reference deficits and active adjoint weights follow
from their accepted interval endpoints, rather than sign assumptions. -/
namespace OptimalG.Certificates.Transport.ReferenceWeightCell

def positivityCheck (c : ReferenceWeightCell) : Bool :=
  decide (0<c.deficit.lo ∧ 0<c.terminal.lo) &&
  (List.finRange 4).all (fun i=>decide (0≤(c.weights i).lo ∧
    ((c.flow.late=true ∨ i=1 ∨ i=3) → 0<(c.weights i).lo)))

theorem checked_positivity {s : ℕ} (hs : 0<s) (c : ReferenceWeightCell)
    (hc : c.positivityCheck=true) {Z terminal : ℝ} {w : Fin 4→ℝ}
    (hZ : c.deficit.Contains s Z) (hT : c.terminal.Contains s terminal)
    (hw : ∀ i,(c.weights i).Contains s (w i)) :
    0<Z ∧ 0<terminal ∧ (∀ i,0≤w i) ∧
      (∀ i,c.flow.late=true ∨ i=1 ∨ i=3 → 0<w i) := by
  obtain ⟨hzt,hweights⟩ := Bool.and_eq_true_iff.mp hc
  have hzt' : 0<c.deficit.lo ∧ 0<c.terminal.lo := of_decide_eq_true hzt
  have hweight (i : Fin 4) : 0≤(c.weights i).lo ∧
      ((c.flow.late=true ∨ i=1 ∨ i=3) → 0<(c.weights i).lo) :=
    of_decide_eq_true (List.all_eq_true.mp hweights i (List.mem_finRange i))
  refine ⟨IntegerInterval.positive hs hZ hzt'.1,
    IntegerInterval.positive hs hT hzt'.2,?_,?_⟩
  · intro i
    have hlo : (0:ℝ)≤(c.weights i).lo := by exact_mod_cast (hweight i).1
    have hs' : (0:ℝ)<s := by exact_mod_cast hs
    have hh := (hw i).1
    nlinarith
  · intro i hi
    exact IntegerInterval.positive hs (hw i) ((hweight i).2 hi)

end OptimalG.Certificates.Transport.ReferenceWeightCell
