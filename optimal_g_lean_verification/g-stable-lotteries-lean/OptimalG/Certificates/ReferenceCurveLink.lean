import OptimalG.Certificates.ReferenceFlowField
import OptimalG.Certificates.CubicLookup

/-! Exact coefficient checks identify each local unit-interval polynomial with
one piece of the globally assembled C¹ reference curve. -/
namespace OptimalG.Certificates
open Set

def polynomialPieceCheck (p : RationalPolynomial) (lo hi : ℚ) (q : CubicPiece) : Bool :=
  decide (q.lo=lo ∧ q.hi=hi ∧ q.a3=0 ∧
    p=[q.f0,q.a0*(hi-lo),(q.a1/2)*(hi-lo)^2,(q.a2/3)*(hi-lo)^3])

theorem polynomialPieceCheck_values {p : RationalPolynomial} {lo hi : ℚ} {q : CubicPiece}
    (hc : polynomialPieceCheck p lo hi q=true) (htime : lo<hi) (t : ℝ) :
    p.eval t=q.primitive (((hi:ℝ)-lo)*t) ∧
    p.derivative.eval t/((hi:ℝ)-lo)=q.score (((hi:ℝ)-lo)*t) := by
  have hh : q.lo=lo ∧ q.hi=hi ∧ q.a3=0 ∧
      p=[q.f0,q.a0*(hi-lo),(q.a1/2)*(hi-lo)^2,(q.a2/3)*(hi-lo)^3] :=
    of_decide_eq_true hc
  have hlen : (hi:ℝ)-(lo:ℝ)≠0 := ne_of_gt (by exact_mod_cast (sub_pos.mpr htime))
  rw [hh.2.2.2]
  constructor
  · simp [RationalPolynomial.eval,CubicPiece.primitive,hh.2.2.1]
    ring
  · simp [RationalPolynomial.derivative,RationalPolynomial.eval_add,RationalPolynomial.eval,
      CubicPiece.score,hh.2.2.1]
    field_simp
    ring

theorem polynomialPieceCheck_global {p : RationalPolynomial} {lo hi L S : ℚ}
    {q : CubicPiece} {pieces : List CubicPiece}
    (hc : polynomialPieceCheck p lo hi q=true) (htime : lo<hi)
    (hlookup : cubicLookupCheck q pieces=true)
    (hscore : Continuous (cubicScore L pieces))
    (hprimitive : Continuous (cubicPrimitive L S pieces))
    {z : ℝ} (hz : z∈Icc (lo:ℝ) hi) :
    p.eval ((z-lo)/((hi:ℝ)-lo))=cubicPrimitive L S pieces z ∧
    p.derivative.eval ((z-lo)/((hi:ℝ)-lo))/((hi:ℝ)-lo)=cubicScore L pieces z := by
  have hh : q.lo=lo ∧ q.hi=hi ∧ q.a3=0 ∧
      p=[q.f0,q.a0*(hi-lo),(q.a1/2)*(hi-lo)^2,(q.a2/3)*(hi-lo)^3] :=
    of_decide_eq_true hc
  have hq : q.lo<q.hi := by simpa only [hh.1,hh.2.1] using htime
  have hzq : z∈Icc (q.lo:ℝ) q.hi := by simpa only [hh.1,hh.2.1] using hz
  have hv := polynomialPieceCheck_values hc htime ((z-lo)/((hi:ℝ)-lo))
  have hg := cubicLookupCheck_closed_values hlookup hq L S hscore hprimitive hzq
  have hlen : (hi:ℝ)-(lo:ℝ)≠0 := ne_of_gt (by exact_mod_cast (sub_pos.mpr htime))
  have he : ((hi:ℝ)-lo)*((z-lo)/((hi:ℝ)-lo))=z-lo := by field_simp
  rw [he] at hv
  rw [hh.1] at hg
  exact And.intro (hv.1.trans hg.2.symm) (hv.2.trans hg.1.symm)

end OptimalG.Certificates
