import OptimalG.Certificates.ReferenceDataEquality
import OptimalG.Certificates.ReferencePositionCell
import OptimalG.Certificates.ReferenceRefinedWeights
import OptimalG.Certificates.ReferenceEndpointLink

/-! Positional first-variation certificates use the very same exponential,
terminal value and enclosed reference flow as the weight certificates. The
change of integer scale and the error radius are checked explicitly. -/
namespace OptimalG.Certificates.Transport.ReferencePositionCell
open Set

def inputLinkCheck (s multiplier : ℕ) (c : ReferencePositionCell)
    (w : ReferenceWeightCertificate) : Bool :=
  decide (c.cell.flow=w.cell.flow ∧ c.exponential=w.cell.exponential.rescale multiplier ∧
    c.terminal=w.cell.terminal.rescale multiplier) &&
  IntegerInterval.centerRadiusCheck (multiplier*s) 0
    (w.cell.flow.valueErrorRadius w.start) c.flowError

theorem inputLinkCheck_sound {s multiplier : ℕ} (hm : 0<multiplier)
    {c : ReferencePositionCell} {w : ReferenceWeightCertificate}
    (hc : c.inputLinkCheck s multiplier w=true)
    {t E Z terminal : ℝ}
    (hE : w.cell.exponential.Contains s E) (hT : w.cell.terminal.Contains s terminal)
    (herr : |Z-w.cell.flow.valuePolynomial.eval t|≤(w.cell.flow.valueErrorRadius w.start:ℝ)) :
    c.exponential.Contains (multiplier*s) E ∧
    c.terminal.Contains (multiplier*s) terminal ∧
    c.flowError.Contains (multiplier*s) (Z-c.cell.flow.valuePolynomial.eval t) := by
  obtain ⟨hlink,herror⟩ := Bool.and_eq_true_iff.mp hc
  have hl : c.cell.flow=w.cell.flow ∧ c.exponential=w.cell.exponential.rescale multiplier ∧
      c.terminal=w.cell.terminal.rescale multiplier := of_decide_eq_true hlink
  refine ⟨?_,?_,?_⟩
  · rw [hl.2.1]
    exact (IntegerInterval.rescale_contains_iff hm s _ _).mpr hE
  · rw [hl.2.2]
    exact (IntegerInterval.rescale_contains_iff hm s _ _).mpr hT
  · apply IntegerInterval.centerRadiusCheck_sound herror
    simpa only [Rat.cast_zero,sub_zero,hl.1] using herr

theorem checked_linked_force {s multiplier k : ℕ} (hs : 0<s)
    (hm : 0<multiplier) (hk : 0<k) (c : ReferencePositionCell)
    (w : ReferenceWeightCertificate)
    (hc : c.check (multiplier*s) k=true)
    (hl : c.inputLinkCheck s multiplier w=true)
    {t E Z terminal : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hE : w.cell.exponential.Contains s E) (hT : w.cell.terminal.Contains s terminal)
    (herr : |Z-w.cell.flow.valuePolynomial.eval t|≤(w.cell.flow.valueErrorRadius w.start:ℝ)) :
    c.force.Contains (multiplier*s)
      (E*((RatExpr.partialExpr c.coordinate c.cell.alphaSource).eval (c.cell.frozenInput t)*Z+
        (RatExpr.partialExpr c.coordinate c.cell.betaSource).eval (c.cell.frozenInput t))/terminal) := by
  obtain ⟨he,htm,herror⟩ := inputLinkCheck_sound hm hl hE hT herr
  exact c.checked_force (Nat.mul_pos hm hs) hk hc ht he htm herror

end OptimalG.Certificates.Transport.ReferencePositionCell
