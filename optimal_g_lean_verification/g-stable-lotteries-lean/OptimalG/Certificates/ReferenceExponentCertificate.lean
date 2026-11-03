import OptimalG.Certificates.ReferenceWeightCertificate
import OptimalG.Certificates.IntegralIntervalBounds

/-! The exponent input of each weight certificate encloses the actual suffix
integral of the affine coefficient. It is assembled from a checked cumulative
integral and the current cell's partial integral. -/
namespace OptimalG.Certificates.Transport
open Set MeasureTheory

structure ReferenceExponentCertificate where
  weight : ReferenceWeightCertificate
  future : IntegerInterval
  partialExponent : IntegerInterval

namespace ReferenceExponentCertificate

def interval (c : ReferenceExponentCertificate) : IntegralCell :=
  ⟨c.weight.cell.flow.segment.left.z,c.weight.cell.flow.segment.right.z,c.weight.mass,c.future⟩

def check (s : ℕ) (c : ReferenceExponentCertificate) : Bool :=
  IntegerInterval.partialIntegralCheck s c.interval.lo c.interval.hi c.weight.alphaBounds
    c.partialExponent &&
  (c.partialExponent.addRounded c.future).subsetCheck c.weight.cell.exponent

theorem checked_exponent {s : ℕ} (hs : 0<s) (c : ReferenceExponentCertificate)
    (hc : c.check s=true) {alpha : ℝ→ℝ} {z finish : ℝ}
    (hz : z∈Icc (c.interval.lo:ℝ) c.interval.hi)
    (hi : IntervalIntegrable alpha volume (c.interval.lo:ℝ) c.interval.hi)
    (hfuture : IntervalIntegrable alpha volume (c.interval.hi:ℝ) finish)
    (hbound : ∀ᵐ x ∂volume.restrict (Icc (c.interval.lo:ℝ) c.interval.hi),
      c.weight.alphaBounds.Contains s (alpha x))
    (hF : c.future.Contains s (∫ x in (c.interval.hi:ℝ)..finish,alpha x)) :
    c.weight.cell.exponent.Contains s (∫ x in z..finish,alpha x) := by
  obtain ⟨hp,ha⟩ := Bool.and_eq_true_iff.mp hc
  exact IntegerInterval.cumulative_contains hs hp ha hz hi hfuture hbound hF

end ReferenceExponentCertificate
end OptimalG.Certificates.Transport
