import OptimalG.Certificates.StaticLayerArithmetic
import OptimalG.Certificates.Bernstein7

/-! Degree-seven positivity checks avoid reconstructing a Bernstein expansion
separately for every cell. The fixed formula identity was proved once. -/
namespace OptimalG.Certificates.StaticSupport.ContinuousLayerCell
open RationalPolynomial

def fastNumericCheck (c : ContinuousLayerCell) : Bool := c.numericPolynomials.all fixed7Check

theorem fastNumericCheck_nonnegative {c : ContinuousLayerCell} (hc : c.fastNumericCheck=true)
    {p : RationalPolynomial} (hp : p∈c.numericPolynomials) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0≤p.eval t := fixed7Check_sound (List.all_eq_true.mp hc p hp) ht

theorem fastNumericCheck_sound {c : ContinuousLayerCell} (hc : c.fastNumericCheck=true)
    {t : ℝ} (ht : t∈Set.Icc 0 1) :
    0<c.Rnum.eval t/c.Rden.eval t ∧
    c.Rnum.eval t/c.Rden.eval t*c.A.eval t+c.P.eval t*c.B.eval t≤
      c.Cnum.eval t/c.Cden.eval t*
        (c.h.eval t*(c.Rnum.eval t/c.Rden.eval t)-c.k.eval t*c.P.eval t) ∧
    c.Cnum.eval t/c.Cden.eval t≤c.Cu.eval t ∧
    (c.B.eval t+c.Cnum.eval t/c.Cden.eval t*c.k.eval t)/
      (c.Rnum.eval t/c.Rden.eval t)≤c.alphau.eval t :=
  polynomials_sound (fun _ hp => fastNumericCheck_nonnegative hc hp ht)

theorem fastNumericCheck_pin_bounds {c : ContinuousLayerCell} (hc : c.fastNumericCheck=true)
    (hpin : c.pinned=true) {t : ℝ} (ht : t∈Set.Icc 0 1) :
    (1/10:ℝ)≤c.Cnum.eval t/c.Cden.eval t ∧
      c.Cnum.eval t/c.Cden.eval t≤-(StaticLow.slopeQ StaticLow.leftContact:ℝ) :=
  polynomials_pin_bounds (fun _ hp => fastNumericCheck_nonnegative hc hp ht) hpin

end OptimalG.Certificates.StaticSupport.ContinuousLayerCell
