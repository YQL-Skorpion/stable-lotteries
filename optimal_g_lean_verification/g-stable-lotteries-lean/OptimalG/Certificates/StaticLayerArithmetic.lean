import OptimalG.Certificates.StaticLayerPolynomials

/-! Sound denominator clearing for continuous support certificates. -/
namespace OptimalG.Certificates.StaticSupport

private theorem cleared_support_inequalities {rn rd cn cd h k P A B Cu au : ℝ}
    (hrn : 0<rn) (hrd : 0<rd) (hcd : 0<cd)
    (hb : 0≤cn*(h*rn-k*P*rd)-(rn*A+P*B*rd)*cd)
    (hC : 0≤Cu*cd-cn)
    (ha : 0≤au*cd*rn-rd*(B*cd+cn*k)) :
    0<rn/rd ∧ rn/rd*A+P*B≤cn/cd*(h*(rn/rd)-k*P) ∧
      cn/cd≤Cu ∧ (B+cn/cd*k)/(rn/rd)≤au := by
  have hbal := div_nonneg hb (mul_pos hcd hrd).le
  have he : (cn*(h*rn-k*P*rd)-(rn*A+P*B*rd)*cd)/(cd*rd)=
      cn/cd*(h*(rn/rd)-k*P)-(rn/rd*A+P*B) := by
    field_simp
    try ring
  rw [he] at hbal
  have hcoef : cn/cd≤Cu := (div_le_iff₀ hcd).mpr (by linarith only [hC])
  have ha' := div_nonneg ha (mul_pos hcd hrn).le
  have he' : (au*cd*rn-rd*(B*cd+cn*k))/(cd*rn)=au-(B+cn/cd*k)/(rn/rd) := by
    field_simp
    try ring
  rw [he'] at ha'
  exact ⟨div_pos hrn hrd,by linarith only [hbal],hcoef,by linarith only [ha']⟩

namespace ContinuousLayerCell
open RationalPolynomial

theorem polynomials_positive {c : ContinuousLayerCell} {t : ℝ}
    (hc : ∀ p∈c.numericPolynomials, 0≤p.eval t) :
    0<c.Rnum.eval t ∧ 0<c.Rden.eval t ∧ 0<c.Cden.eval t := by
  have h1 := hc (add c.Rnum [-1/100]) (by simp [numericPolynomials])
  have h2 := hc (add c.Rden [-1/2]) (by simp [numericPolynomials])
  have h3 := hc (add c.Cden [-1/100]) (by simp [numericPolynomials])
  norm_num [eval_add,RationalPolynomial.eval] at h1 h2 h3
  exact ⟨by linarith,by linarith,by linarith⟩

/-- All support inequalities at every real point of the unit parameter interval.
No statement about the sampled endpoints is used in this theorem. -/
theorem polynomials_sound {c : ContinuousLayerCell} {t : ℝ}
    (hc : ∀ p∈c.numericPolynomials, 0≤p.eval t) :
    0<c.Rnum.eval t/c.Rden.eval t ∧
    c.Rnum.eval t/c.Rden.eval t*c.A.eval t+c.P.eval t*c.B.eval t≤
      c.Cnum.eval t/c.Cden.eval t*
        (c.h.eval t*(c.Rnum.eval t/c.Rden.eval t)-c.k.eval t*c.P.eval t) ∧
    c.Cnum.eval t/c.Cden.eval t≤c.Cu.eval t ∧
    (c.B.eval t+c.Cnum.eval t/c.Cden.eval t*c.k.eval t)/
      (c.Rnum.eval t/c.Rden.eval t)≤c.alphau.eval t := by
  have hp := polynomials_positive hc
  have hb := hc c.balancePolynomial
    (by simp [numericPolynomials])
  have hC := hc c.coefficientPolynomial
    (by simp [numericPolynomials])
  have ha := hc c.alphaPolynomial
    (by simp [numericPolynomials])
  simp only [balancePolynomial,D,N,coefficientPolynomial,alphaPolynomial,
    eval_add,eval_mul,eval_scale,Rat.cast_neg,Rat.cast_one] at hb hC ha
  apply cleared_support_inequalities hp.1 hp.2.1 hp.2.2
  · linarith only [hb]
  · linarith only [hC]
  · linarith only [ha]

theorem polynomials_pin_bounds {c : ContinuousLayerCell} {t : ℝ}
    (hc : ∀ p∈c.numericPolynomials, 0≤p.eval t) (hpin : c.pinned=true) :
    (1/10:ℝ)≤c.Cnum.eval t/c.Cden.eval t ∧
      c.Cnum.eval t/c.Cden.eval t≤-(StaticLow.slopeQ StaticLow.leftContact:ℝ) := by
  have hp := (polynomials_positive hc).2.2
  have hl := hc c.pinLowerPolynomial
    (by simp [numericPolynomials,hpin])
  have hu := hc c.pinUpperPolynomial
    (by simp [numericPolynomials,hpin])
  simp only [pinLowerPolynomial,pinUpperPolynomial,eval_add,eval_scale,
    Rat.cast_div,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat] at hl hu
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith only [hl]
  · apply (div_le_iff₀ hp).mpr
    linarith only [hu]

end ContinuousLayerCell
end OptimalG.Certificates.StaticSupport
