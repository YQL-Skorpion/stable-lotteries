import OptimalG.ExtendedTailAssembly
import OptimalG.Certificates.ExtendedSelectedData.HeadLateInactive
import OptimalG.Certificates.StaticExtendedTailDataBatch02
import OptimalG.Certificates.StaticExtendedTailDataBatch01
import OptimalG.Certificates.StaticExtendedTailDataBatch00

/-! Accepted finite Bernstein signs discharge every fixed-anchor tail
family. The remaining analytic rank coverage is ExtendedTailAssembly. -/
namespace OptimalG.Certificates.StaticExtendedTailChecks
open Set StaticExtendedTailData ExtendedTailExpressions

theorem polynomial_signs_lo {p t : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (19/50:ℝ) (StaticLow.lam:ℝ)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    ExtendedTailPolynomialSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p t (-(3589/10000)) := by
  have hpall : p∈Icc (19/50:ℝ) (56233/100000) := ⟨hp.1,hp.2.trans hL.2⟩
  constructor
  · intro hp45 z hz
    have hh := HeadSquareLo.numerator_pos ⟨hp45,hpall.2⟩ hz ht
    rw [HeadSquareLo.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro hp45 z hz
    have hh := HeadInactiveLo.numerator_pos ⟨hp.1,hp45⟩ hz ht
    rw [HeadInactiveLo.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro hp45
    have hh := ExtendedSelectedData.HeadLateInactive.numerator_pos (z:=0)
      hL hS ⟨hp.1,hp45⟩ (by norm_num) ht
    rw [ExtendedSelectedData.HeadLateInactive.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro z hz
    constructor
    · have hh := HighHeadLo.numerator_pos hpall hz ht
      rw [HighHeadLo.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := HighMassLo.numerator_pos hpall hz ht
      rw [HighMassLo.expression_identity] at hh
      exact (neg_pos.mp hh).le
  · intro hp515 u hu
    constructor
    · have hh := CapZeroLo.numerator_pos ⟨hp515,hpall.2⟩ hu ht
      rw [CapZeroLo.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := CapLineLo.numerator_pos ⟨hp515,hpall.2⟩ hu ht
      rw [CapLineLo.expression_identity] at hh
      exact (neg_pos.mp hh).le

theorem polynomial_signs_hi {p t : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (19/50:ℝ) (StaticLow.lam:ℝ)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    ExtendedTailPolynomialSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p t (-(1757/5000)) := by
  have hpall : p∈Icc (19/50:ℝ) (56233/100000) := ⟨hp.1,hp.2.trans hL.2⟩
  constructor
  · intro hp45 z hz
    have hh := HeadSquareHi.numerator_pos ⟨hp45,hpall.2⟩ hz ht
    rw [HeadSquareHi.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro hp45 z hz
    have hh := HeadInactiveHi.numerator_pos ⟨hp.1,hp45⟩ hz ht
    rw [HeadInactiveHi.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro hp45
    have hh := ExtendedSelectedData.HeadLateInactive.numerator_pos (z:=0)
      hL hS ⟨hp.1,hp45⟩ (by norm_num) ht
    rw [ExtendedSelectedData.HeadLateInactive.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro z hz
    constructor
    · have hh := HighHeadHi.numerator_pos hpall hz ht
      rw [HighHeadHi.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := HighMassHi.numerator_pos hpall hz ht
      rw [HighMassHi.expression_identity] at hh
      exact (neg_pos.mp hh).le
  · intro hp515 u hu
    constructor
    · have hh := CapZeroHi.numerator_pos ⟨hp515,hpall.2⟩ hu ht
      rw [CapZeroHi.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := CapLineHi.numerator_pos ⟨hp515,hpall.2⟩ hu ht
      rw [CapLineHi.expression_identity] at hh
      exact (neg_pos.mp hh).le

end OptimalG.Certificates.StaticExtendedTailChecks
