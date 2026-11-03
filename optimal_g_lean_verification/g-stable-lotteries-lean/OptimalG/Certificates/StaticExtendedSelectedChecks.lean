import OptimalG.ExtendedSelectedFiniteTargets
import OptimalG.Certificates.ExtendedLocalChecks
import OptimalG.Certificates.StaticExtendedSelectedData.HighRankHeadZero
import OptimalG.Certificates.StaticExtendedSelectedDataBatch03
import OptimalG.Certificates.StaticExtendedSelectedDataBatch02
import OptimalG.Certificates.StaticExtendedSelectedDataBatch01
import OptimalG.Certificates.StaticExtendedSelectedDataBatch00

/-! Numerical instantiation of the explicit finite selected-high targets.
Every imported sign is a reconstructed rational Bernstein certificate. -/
namespace OptimalG.Certificates.StaticExtendedSelectedChecks
open Set StaticExtendedSelectedData ExtendedSelectedExpressions

theorem polynomial_signs {p t : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (19/50:ℝ) (StaticLow.lam:ℝ)) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    ExtendedSelectedPolynomialSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p t := by
  have hpall : p∈Icc (19/50:ℝ) (56233/100000) := ⟨hp.1,hp.2.trans hL.2⟩
  constructor
  · intro z hz e he
    have he' : e∈Icc (0:ℝ) (17/5000) := by
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl <;> norm_num
    exact (ExtendedLocalChecks.localCore_neg hL hS ⟨by linarith only [hp.1],hpall.2⟩ hz ht he').le
  · intro e he
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl
    · have hh := HeadEarlyZero.numerator_pos (z:=0) hpall (by norm_num) ht
      rw [HeadEarlyZero.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := HeadEarlyMax.numerator_pos (z:=0) hpall (by norm_num) ht
      rw [HeadEarlyMax.expression_identity] at hh
      exact (neg_pos.mp hh).le
  · intro hp45 e he
    have hpl : p∈Icc (9/20:ℝ) (56233/100000) := ⟨hp45,hpall.2⟩
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl
    · have hh := HeadLateZero.numerator_pos (z:=0) hpl (by norm_num) ht
      rw [HeadLateZero.expression_identity] at hh
      exact (neg_pos.mp hh).le
    · have hh := HeadLateMax.numerator_pos (z:=0) hpl (by norm_num) ht
      rw [HeadLateMax.expression_identity] at hh
      exact (neg_pos.mp hh).le
  · intro hp45
    have hh := HeadLateInactive.numerator_pos (z:=0) ⟨hp.1,hp45⟩ (by norm_num) ht
    rw [HeadLateInactive.expression_identity] at hh
    exact (neg_pos.mp hh).le
  · intro z hz e he
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl
    · constructor
      · have hh := HighRankHeadZero.numerator_pos hpall hz ht
        rw [HighRankHeadZero.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := HighRankMassZero.numerator_pos hpall hz ht
        rw [HighRankMassZero.expression_identity] at hh
        exact (neg_pos.mp hh).le
    · constructor
      · have hh := HighRankHeadMax.numerator_pos hpall hz ht
        rw [HighRankHeadMax.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := HighRankMassMax.numerator_pos hpall hz ht
        rw [HighRankMassMax.expression_identity] at hh
        exact (neg_pos.mp hh).le
  · intro hpr u hu e he
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl
    · constructor
      · have hh := CapZeroZeroTriangle.numerator_pos hpr hu ht
        rw [CapZeroZeroTriangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := CapLineZeroTriangle.numerator_pos hpr hu ht
        rw [CapLineZeroTriangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
    · constructor
      · have hh := CapZeroMaxTriangle.numerator_pos hpr hu ht
        rw [CapZeroMaxTriangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := CapLineMaxTriangle.numerator_pos hpr hu ht
        rw [CapLineMaxTriangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
  · intro hp515 u hu e he
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : e=0 ∨ e=17/5000) with rfl | rfl
    · constructor
      · have hh := CapZeroZeroRectangle.numerator_pos ⟨hp515,hpall.2⟩ hu ht
        rw [CapZeroZeroRectangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := CapLineZeroRectangle.numerator_pos ⟨hp515,hpall.2⟩ hu ht
        rw [CapLineZeroRectangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
    · constructor
      · have hh := CapZeroMaxRectangle.numerator_pos ⟨hp515,hpall.2⟩ hu ht
        rw [CapZeroMaxRectangle.expression_identity] at hh
        exact (neg_pos.mp hh).le
      · have hh := CapLineMaxRectangle.numerator_pos ⟨hp515,hpall.2⟩ hu ht
        rw [CapLineMaxRectangle.expression_identity] at hh
        exact (neg_pos.mp hh).le

theorem all_checks {p t : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (19/50:ℝ) (StaticLow.lam:ℝ)) (ht : t∈Icc (1529/5000:ℝ) (9/25))
    (hJ : 0<ExtendedScalarExpressions.betaNumerator (StaticLow.lam:ℝ) p t)
    (hs : 0<1+SmallMassExpressions.slope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) :
    OptimalG.ExtendedSelectedChecks (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p t :=
  (polynomial_signs hL hS hp ht).toChecks hp.1 hJ hs

end OptimalG.Certificates.StaticExtendedSelectedChecks
