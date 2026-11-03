import OptimalG.Certificates.ReferenceWeightCell
import OptimalG.Certificates.ReferenceQuadrature
import OptimalG.Certificates.ReferenceValueCell

/-! A single finite record keeps each refined field integral, pointwise field
bound and actual-flow weight bound together. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

structure ReferenceWeightCertificate where
  cell : ReferenceWeightCell
  start : ℚ
  mean : IntegerInterval
  mass : IntegerInterval
  alphaBounds : IntegerInterval

namespace ReferenceWeightCertificate

def check (s k : ℕ) (c : ReferenceWeightCertificate) : Bool :=
  c.cell.flow.alphaExpr.midpointScaledIntegralCheck s k c.cell.flow.length c.mean c.mass &&
  c.cell.flow.alphaExpr.cleanup.enclosureRefinedCheck s k (fun _ => ⟨0,s⟩) c.alphaBounds &&
  c.cell.flow.actualValueCheck s k c.start c.cell.deficit && c.cell.check s k

theorem checked_integral {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true) :
    c.mass.Contains s ((c.cell.flow.length:ℝ)*
      (∫ t in (0:ℝ)..1,c.cell.flow.actualAlpha t)) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  have h := RatExpr.midpointScaledIntegralCheck_sound hs hk c.cell.flow.alphaExpr
    c.cell.flow.length c.mean c.mass hh.1.1.1
  simpa only [ReferenceFlowCell.alphaExpr_eval] using h

theorem checked_alpha {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : c.alphaBounds.Contains s (c.cell.flow.actualAlpha t) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  have hu : ∀ i : Fin 1,(⟨0,(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro i
    exact ⟨by simpa using mul_nonneg (Nat.cast_nonneg s) ht.1,
      by simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)⟩
  have h := RatExpr.enclosureRefinedCheck_sound hs hk c.cell.flow.alphaExpr.cleanup
    (fun _ => ⟨0,s⟩) c.alphaBounds hh.1.1.2 (fun _ => t) hu
  rw [RatExpr.cleanup_eval] at h
  change c.alphaBounds.Contains s (c.cell.flow.alphaExpr.evalOne t) at h
  rwa [ReferenceFlowCell.alphaExpr_eval] at h

theorem checked_weights {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceWeightCertificate) (hc : c.check s k=true)
    {t exponent Z terminal : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (he : c.cell.exponent.Contains s exponent)
    (herror : |Z-c.cell.flow.valuePolynomial.eval t|≤(c.cell.flow.valueErrorRadius c.start:ℝ))
    (hterm : c.cell.terminal.Contains s terminal) (i : Fin 4) :
    (c.cell.weights i).Contains s
      (Real.exp exponent*(c.cell.flow.baseCoefficientExpr i).evalOne t*
        (if i<2 then Z else 1)/terminal) := by
  have hh := hc
  simp only [check,Bool.and_eq_true] at hh
  exact c.cell.checked_weights hs hk hh.2 ht he
    (c.cell.flow.actualValueCheck_sound hs hk c.start c.cell.deficit hh.1.2 ht herror) hterm i

end ReferenceWeightCertificate
end OptimalG.Certificates.Transport
