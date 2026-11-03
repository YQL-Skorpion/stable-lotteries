import OptimalG.Certificates.ExtendedScalarExpressions
import OptimalG.DefectBounds

/-! Exact cleared comparison used by the extended C.4 high tests. The two
low-rank arguments are bounded by genuine cumulative/remaining slack
envelopes; the selected high deficit is retained with its correct sign. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions

noncomputable def extendedNIncrement (lam S p0 p t : ℝ) : ℝ :=
  (lam-t)*(lam-p0-(p-p0)/2)+(lam-p0)*(1-p0-lam-(p-p0)/2)-
    (quadratic lam (1-p0)-S)-(p-p0)*(1-p0-lam-(p-p0)/2)
noncomputable def extendedDIncrement (lam S p0 p t : ℝ) : ℝ :=
  (2*lam-t)*(lam-p0-(p-p0)/2)-(2*p0-lam)*(1-p0-lam-(p-p0)/2)-
    2*(quadratic lam (1-p0)-S)-2*(p-p0)*(1-p0-lam-(p-p0)/2)
noncomputable def extendedWeightDifference (lam S p0 p t : ℝ) : ℝ :=
  -t*etaNumerator lam S p0 t-extendedDIncrement lam S p0 p t*betaNumerator lam p0 t

noncomputable def extendedHighCore (lam S p t q z e su eu fz : ℝ) : ℝ :=
  denominator lam S p t*(z+q-lam)+betaNumerator lam p t*
    (p*(z-lam-p/2)-q*(z-p)+su+eu+e)+etaNumerator lam S p t*fz

noncomputable def extendedBaseCore (lam S p0 t z e fz : ℝ) : ℝ :=
  denominator lam S p0 t*(z-lam)+betaNumerator lam p0 t*
    (p0*(z-lam-p0/2)+e)+etaNumerator lam S p0 t*fz

noncomputable def extendedCompareCore (lam S p0 p t q z e su eu : ℝ) : ℝ :=
  (p-p0)*((extendedNIncrement lam S p0 p t*etaNumerator lam S p0 t-
      extendedDIncrement lam S p0 p t*denominator lam S p0 t)*(z-lam)+
    betaNumerator lam p t*etaNumerator lam S p0 t*(z-lam-p0-(p-p0)/2)+
    extendedWeightDifference lam S p0 p t*(p0*(z-lam-p0/2)+e))+
  etaNumerator lam S p0 t*(q*(denominator lam S p t-betaNumerator lam p t*(z-p))+
    betaNumerator lam p t*(su+eu))

theorem extended_compare_identity (lam S p0 p t q z e su eu fz : ℝ) :
    extendedCompareCore lam S p0 p t q z e su eu=
      etaNumerator lam S p0 t*extendedHighCore lam S p t q z e su eu fz-
      etaNumerator lam S p t*extendedBaseCore lam S p0 t z e fz := by
  have hN : denominator lam S p t=denominator lam S p0 t+(p-p0)*extendedNIncrement lam S p0 p t := by
    unfold denominator extendedNIncrement quadratic
    ring
  have hD : etaNumerator lam S p t=etaNumerator lam S p0 t+(p-p0)*extendedDIncrement lam S p0 p t := by
    unfold etaNumerator extendedDIncrement quadratic
    ring
  have hJ : betaNumerator lam p t=betaNumerator lam p0 t-(p-p0)*t := by
    unfold betaNumerator
    ring
  unfold extendedCompareCore extendedHighCore extendedBaseCore extendedWeightDifference
  rw [hN,hD,hJ]
  ring

/-- A checked cleared comparison transfers the base high test. Neither the
sign nor the size of the high deficit is altered by this algebraic step. -/
theorem extended_compare_nonpos {lam S p0 p t q z e su eu fz : ℝ}
    (hD0 : 0<etaNumerator lam S p0 t) (hD : 0≤etaNumerator lam S p t)
    (hbase : extendedBaseCore lam S p0 t z e fz≤0)
    (hcompare : extendedCompareCore lam S p0 p t q z e su eu≤0) :
    extendedHighCore lam S p t q z e su eu fz≤0 := by
  have hb := mul_nonpos_of_nonneg_of_nonpos hD hbase
  rw [extended_compare_identity lam S p0 p t q z e su eu fz] at hcompare
  have hh : etaNumerator lam S p0 t*extendedHighCore lam S p t q z e su eu fz≤0 := by
    linarith only [hb,hcompare]
  by_contra hn
  have hp := mul_pos hD0 (lt_of_not_ge hn)
  linarith only [hh,hp]

/-- The two primitive envelopes imply the precise upper bound used in the
cleared high residual. This applies also when the delayed rank is above the
low transition, provided its stated envelope remains valid. -/
theorem packingK_bound_from_slacks {phi : ℝ→ℝ} {lam S p q z su eu : ℝ}
    (hslack : quadratic lam q-curvePrimitive phi q≤su)
    (hremaining : curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤eu) :
    packingK phi p q z≤p*(z-lam-p/2)-q*(z-p)+su+eu+primitiveDefect phi lam S z := by
  unfold packingK primitiveDefect quadratic at *
  nlinarith only [hslack,hremaining]

theorem packingK_zero_of_middle_shift {phi : ℝ→ℝ} {lam S p z : ℝ}
    (hshift : curvePrimitive phi (z-p)=quadratic lam (z-p)-S) :
    packingK phi p 0 z=p*(z-lam-p/2)+primitiveDefect phi lam S z := by
  rw [packingK,add_zero,hshift]
  have hz : curvePrimitive phi 0=0 := by simp [curvePrimitive]
  rw [hz]
  unfold primitiveDefect quadratic
  ring

end OptimalG
