import OptimalG.LargeTailBeforeAssembly
import OptimalG.LargeTailHighAssembly
import OptimalG.Certificates.IntervalParameter

/-! Exact parameter coverage for the nonrectangular head/cap corner tests.
The triangle boundary is included even when its width is zero. -/
namespace OptimalG
open Set Variational Certificates.LargeTailExpressions

structure LargeTailLineRegionSigns (lam S H : ℝ) : Prop where
  square : ∀ p∈Icc (13/20:ℝ) (391/500),∀ z∈Icc (7/8:ℝ) (97/100),
    headCleared lam S p (massCap lam S p) z (8793/100000) H≤0
  capFlat : ∀ p∈Icc (13/20:ℝ) (391/500),∀ z∈Icc (7/8:ℝ) (97/100),
    capCore lam S p (massCap lam S p) z (8793/100000) H (313/1000-z+p)≤0
  headZeroTriangle : ∀ p∈Icc (13/20:ℝ) (1413/2000),∀ u∈Icc (0:ℝ) 1,
    headLow lam S p (massCap lam S p) (7/8+u*(p-1223/2000)) (8793/100000) H 0≤0
  headJoinTriangle : ∀ p∈Icc (13/20:ℝ) (1413/2000),∀ u∈Icc (0:ℝ) 1,
    headLow lam S p (massCap lam S p) (7/8+u*(p-1223/2000)) (8793/100000) H
      (527/2000-(7/8+u*(p-1223/2000))+p)≤0
  headZeroRectangle : ∀ p∈Icc (1413/2000:ℝ) (391/500),∀ z∈Icc (7/8:ℝ) (97/100),
    headLow lam S p (massCap lam S p) z (8793/100000) H 0≤0
  headJoinRectangle : ∀ p∈Icc (1413/2000:ℝ) (391/500),∀ z∈Icc (7/8:ℝ) (97/100),
    headLow lam S p (massCap lam S p) z (8793/100000) H (527/2000-z+p)≤0
  capZeroRectangle : ∀ p∈Icc (13/20:ℝ) (657/1000),∀ u∈Icc (0:ℝ) 1,
    capCore lam S p (massCap lam S p) (p+527/2000+u*(313/1000-527/2000)) (8793/100000) H 0≤0
  capZeroTriangle : ∀ p∈Icc (657/1000:ℝ) (1413/2000),∀ u∈Icc (0:ℝ) 1,
    capCore lam S p (massCap lam S p) (p+527/2000+u*(97/100-p-527/2000)) (8793/100000) H 0≤0

structure LargeTailCurvedRegionSigns (lam S H : ℝ) (M : ℝ→ℝ) : Prop where
  square : ∀ p∈Icc (391/500:ℝ) (41/50),∀ z∈Icc (7/8:ℝ) (97/100),
    headCleared lam S p (M p) z (8793/100000) H≤0
  capFlat : ∀ p∈Icc (391/500:ℝ) (41/50),∀ z∈Icc (7/8:ℝ) (97/100),
    capCore lam S p (M p) z (8793/100000) H (313/1000-z+p)≤0
  headZero : ∀ p∈Icc (391/500:ℝ) (41/50),∀ z∈Icc (7/8:ℝ) (97/100),
    headLow lam S p (M p) z (8793/100000) H 0≤0
  headJoin : ∀ p∈Icc (391/500:ℝ) (41/50),∀ z∈Icc (7/8:ℝ) (97/100),
    headLow lam S p (M p) z (8793/100000) H (527/2000-z+p)≤0

theorem LargeTailLineRegionSigns.cover {lam S p z H : ℝ}
    (hn : LargeTailLineRegionSigns lam S H)
    (hp : p∈Icc (13/20:ℝ) (391/500)) (hz : z∈Icc (7/8:ℝ) (97/100))
    (hh : LargeTailHighSigns lam S p (massCap lam S p) z (8793/100000) H) :
    LargeTailSplitSigns lam S p (massCap lam S p) z (8793/100000) H := by
  have head (hd : z-p≤527/2000) :
      headLow lam S p (massCap lam S p) z (8793/100000) H 0≤0 ∧
      headLow lam S p (massCap lam S p) z (8793/100000) H (527/2000-z+p)≤0 := by
    by_cases hpm : p≤1413/2000
    · obtain ⟨u,hu,he⟩ := Certificates.exists_unit_interval_parameter
        (show z∈Icc (7/8:ℝ) (p+527/2000) from ⟨hz.1,by linarith only [hd]⟩)
      have he' : z=7/8+u*(p-1223/2000) := by linarith only [he]
      rw [he']
      exact ⟨hn.headZeroTriangle p ⟨hp.1,hpm⟩ u hu,hn.headJoinTriangle p ⟨hp.1,hpm⟩ u hu⟩
    · exact ⟨hn.headZeroRectangle p ⟨le_of_not_ge hpm,hp.2⟩ z hz,
        hn.headJoinRectangle p ⟨le_of_not_ge hpm,hp.2⟩ z hz⟩
  refine ⟨fun hd=>(head hd).1,fun hd=>(head hd).2,?_,fun _=>hn.capFlat p hp z hz,
    hn.square p hp z hz,hh.cap,hh.left,hh.right,hh.kink⟩
  intro hlo hhi
  by_cases hpm : p≤657/1000
  · obtain ⟨u,hu,he⟩ := Certificates.exists_unit_interval_parameter
      (show z∈Icc (p+527/2000) (p+313/1000) from
        ⟨by linarith only [hlo],by linarith only [hhi]⟩)
    have he' : z=p+527/2000+u*(313/1000-527/2000) := by linarith only [he]
    rw [he']
    exact hn.capZeroRectangle p ⟨hp.1,hpm⟩ u hu
  · have hptop : p≤1413/2000 := by linarith only [hlo,hz.2]
    obtain ⟨u,hu,he⟩ := Certificates.exists_unit_interval_parameter
      (show z∈Icc (p+527/2000) (97/100:ℝ) from ⟨by linarith only [hlo],hz.2⟩)
    have he' : z=p+527/2000+u*(97/100-p-527/2000) := by linarith only [he]
    rw [he']
    exact hn.capZeroTriangle p ⟨le_of_not_ge hpm,hptop⟩ u hu

theorem LargeTailCurvedRegionSigns.cover {lam S p z H : ℝ} {M : ℝ→ℝ}
    (hn : LargeTailCurvedRegionSigns lam S H M)
    (hp : p∈Icc (391/500:ℝ) (41/50)) (hz : z∈Icc (7/8:ℝ) (97/100))
    (hh : LargeTailHighSigns lam S p (M p) z (8793/100000) H) :
    LargeTailSplitSigns lam S p (M p) z (8793/100000) H := by
  refine ⟨fun _=>hn.headZero p hp z hz,fun _=>hn.headJoin p hp z hz,?_,
    fun _=>hn.capFlat p hp z hz,hn.square p hp z hz,hh.cap,hh.left,hh.right,hh.kink⟩
  intro hlo _
  exfalso
  linarith only [hp.1,hz.2,hlo]

end OptimalG
