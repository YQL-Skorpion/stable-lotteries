import OptimalG.DefectBounds
import OptimalG.TailControl

/-! Three scalar endpoint tests suffice for the C.22 small-mass strip. The
piecewise affine/quadratic comparison is proved for all real high ranks. -/
namespace OptimalG
open Set

noncomputable def smallMassDefectProxy (lam p beta eta a b k z : ℝ) : ℝ :=
  (z-lam)*(1+beta*p-eta)-beta*p^2/2+
    (beta*(z-a)/2-eta)*k*max (z-b) 0

theorem smallMassDefectProxy_nonpos {lam p beta eta a b k : ℝ}
    (hab : a≤b) (hb1 : b≤1) (hbeta : 0≤beta) (hk : 0≤k)
    (ha : smallMassDefectProxy lam p beta eta a b k a≤0)
    (hb : smallMassDefectProxy lam p beta eta a b k b≤0)
    (h1 : smallMassDefectProxy lam p beta eta a b k 1≤0) :
    ∀ z∈Icc a 1,smallMassDefectProxy lam p beta eta a b k z≤0 := by
  let v := 1+beta*p-eta
  let A := lam*v+beta*p^2/2-k*(beta*a/2+eta)*b
  let B := -v+k*(beta*(a+b)/2+eta)
  let C := -k*beta/2
  have hleft (t : ℝ) (ht : t≤b) :
      -smallMassDefectProxy lam p beta eta a b k t=(lam*v+beta*p^2/2)+(-v)*t+0*t^2 := by
    unfold smallMassDefectProxy
    rw [max_eq_right (sub_nonpos.mpr ht)]
    dsimp [v]
    ring
  have hright (t : ℝ) (ht : b≤t) :
      -smallMassDefectProxy lam p beta eta a b k t=A+B*t+C*t^2 := by
    unfold smallMassDefectProxy
    rw [max_eq_left (sub_nonneg.mpr ht)]
    dsimp [A,B,C,v]
    ring
  have hC : C≤0 := by dsimp [C]; nlinarith only [mul_nonneg hk hbeta]
  intro z hz
  by_cases hzb : z≤b
  · have hh := quadratic_nonneg_between (lam*v+beta*p^2/2) (-v) 0 a b (by norm_num)
      (by rw [← hleft a hab]; linarith only [ha])
      (by rw [← hleft b le_rfl]; linarith only [hb]) z ⟨hz.1,hzb⟩
    rw [← hleft z hzb] at hh
    linarith only [hh]
  · have hbz := (lt_of_not_ge hzb).le
    have hh := quadratic_nonneg_between A B C b 1 hC
      (by rw [← hright b le_rfl]; linarith only [hb])
      (by rw [← hright 1 hb1]; linarith only [h1]) z ⟨hbz,hz.2⟩
    rw [← hright z hbz] at hh
    linarith only [hh]

namespace VerifierCurve

/-- The finite endpoint conditions imply the actual zero-split third test on
the whole high-rank interval for the C.22 coefficient family. -/
theorem smallMass_third_of_defect_endpoints {phi : ℝ→ℝ} {lam S p beta eta a b k : ℝ}
    (h : VerifierCurve phi lam) (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hla : lam≤a) (hab : a≤b) (hb1 : b≤1) (hbeta : 0≤beta) (hk : 0≤k)
    (hstart : curvePrimitive phi a=Variational.quadratic lam a-S)
    (hzero : phi a=lam-a)
    (hshift : ∀ z∈Icc a 1,
      curvePrimitive phi (z-p)≤Variational.quadratic lam (z-p)-S)
    (hdef : ∀ z∈Icc a 1,k*max (z-b) 0≤scoreDefect phi lam z)
    (hcoef : beta*(1-a)/2-eta≤0)
    (ha : smallMassDefectProxy lam p beta eta a b k a≤0)
    (hb : smallMassDefectProxy lam p beta eta a b k b≤0)
    (h1 : smallMassDefectProxy lam p beta eta a b k 1≤0) :
    ∀ z∈Icc a 1,z-lam+beta*packingK phi p 0 z+eta*phi z≤0 := by
  intro z hz
  have hmain := h.thirdTest_defect_bound (eta := eta) hc hla hz.1 hz.2 hbeta hstart hzero (hshift z hz)
  have hcZ : beta*(z-a)/2-eta≤0 := by
    have hh := mul_le_mul_of_nonneg_left hz.2 hbeta
    linarith only [hh,hcoef]
  have hscaled := mul_le_mul_of_nonpos_left (hdef z hz) hcZ
  have hproxy : z-lam+beta*packingK phi p 0 z+eta*phi z≤
      smallMassDefectProxy lam p beta eta a b k z := by
    unfold smallMassDefectProxy
    nlinarith only [hmain,hscaled]
  exact hproxy.trans (smallMassDefectProxy_nonpos hab hb1 hbeta hk ha hb h1 z hz)

end VerifierCurve
end OptimalG
