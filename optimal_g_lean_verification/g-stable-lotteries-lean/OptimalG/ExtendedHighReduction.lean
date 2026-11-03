import OptimalG.ExtendedHighAlgebra
import OptimalG.ExtendedSlackProfiles

/-! Actual high split tests from explicit cleared scalar residuals. The
comparison residual retains the selected continuation's deficit and then
bounds it on its certified interval. These are analytic bridges only;
finite numerical checks of the displayed scalar functions remain separate. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions

noncomputable def extendedSelectedSlope
    (lam S p0 p t z emax : ℝ) : ℝ :=
  (extendedNIncrement lam S p0 p t*etaNumerator lam S p0 t-
      extendedDIncrement lam S p0 p t*denominator lam S p0 t)*(z-lam)+
    betaNumerator lam p t*etaNumerator lam S p0 t*(z-lam-p0-(p-p0)/2)+
    extendedWeightDifference lam S p0 p t*(p0*(z-lam-p0/2))+
    max (extendedWeightDifference lam S p0 p t) 0*emax

noncomputable def extendedSelectedResidual
    (lam S p0 p t q z emax su eu : ℝ) : ℝ :=
  (p-p0)*extendedSelectedSlope lam S p0 p t z emax+
    etaNumerator lam S p0 t*(q*(denominator lam S p t-betaNumerator lam p t*(z-p))+
      betaNumerator lam p t*(su+eu))

theorem extended_compare_le_selected {lam S p0 p t q z e emax su eu : ℝ}
    (hp : p0≤p) (he : e∈Icc (0:ℝ) emax) :
    extendedCompareCore lam S p0 p t q z e su eu≤
      extendedSelectedResidual lam S p0 p t q z emax su eu := by
  have hw : extendedWeightDifference lam S p0 p t*e≤
      max (extendedWeightDifference lam S p0 p t) 0*emax := by
    calc
      _≤max (extendedWeightDifference lam S p0 p t) 0*e :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) he.1
      _≤_ := mul_le_mul_of_nonneg_left he.2 (le_max_right _ _)
  have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hp)
  unfold extendedCompareCore extendedSelectedResidual extendedSelectedSlope
  nlinarith only [hm]

/-- Restoring the positive denominator turns the cleared residual into the
actual mixed test, after the two primitive envelopes have been proved. -/
theorem extended_high_of_core {phi : ℝ→ℝ} {lam S p t q z su eu : ℝ}
    (hR : curvePrimitive phi p=quadratic lam p-S)
    (hP : curvePrimitive phi (1-p)=quadratic lam (1-p)-S)
    (hN : 0<denominator lam S p t) (hJ : 0≤betaNumerator lam p t)
    (hslack : quadratic lam q-curvePrimitive phi q≤su)
    (hremaining : curvePrimitive phi (z-p+q)-quadratic lam (z-p+q)+S≤eu)
    (hcore : extendedHighCore lam S p t q z (primitiveDefect phi lam S z) su eu (phi z)≤0) :
    z+q-lam+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
      packingK phi p q z+
      extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
  have hK := packingK_bound_from_slacks hslack hremaining
  have hm := mul_le_mul_of_nonneg_left hK hJ
  have hclear : denominator lam S p t*(z+q-lam)+betaNumerator lam p t*packingK phi p q z+
      etaNumerator lam S p t*phi z≤0 := by
    unfold extendedHighCore at hcore
    linarith only [hm,hcore]
  rw [hR,hP,beta_eq,eta_eq]
  apply nonpos_of_mul_nonpos_left (b := denominator lam S p t) _ hN
  convert! hclear using 1 <;> field_simp [hN.ne'] <;> ring

/-- The base zero-split high test is exactly its displayed cleared residual
when its delayed rank is on the middle primitive. -/
theorem extended_baseCore_nonpos {phi : ℝ→ℝ} {lam S p0 t z : ℝ}
    (hR : curvePrimitive phi p0=quadratic lam p0-S)
    (hP : curvePrimitive phi (1-p0)=quadratic lam (1-p0)-S)
    (hN : 0<denominator lam S p0 t)
    (hshift : curvePrimitive phi (z-p0)=quadratic lam (z-p0)-S)
    (hbase : z-lam+extendedBeta lam p0 t (curvePrimitive phi p0) (curvePrimitive phi (1-p0))*
      packingK phi p0 0 z+
      extendedEta lam p0 t (curvePrimitive phi p0) (curvePrimitive phi (1-p0))*phi z≤0) :
    extendedBaseCore lam S p0 t z (primitiveDefect phi lam S z) (phi z)≤0 := by
  rw [hR,hP,beta_eq,eta_eq,packingK_zero_of_middle_shift hshift] at hbase
  have hm := mul_nonpos_of_nonneg_of_nonpos hN.le hbase
  convert! hm using 1 <;> unfold extendedBaseCore <;> field_simp [hN.ne'] <;> ring

/-- On a selected high arc, actual primitive/score geometry and the finite
scalar residual give the full high test at the chosen mass and split. -/
theorem extended_selected_high {phi : ℝ→ℝ} {lam S slope c p t q z pref epsArea epsScore emax : ℝ}
    (h : VerifierCurve phi lam) (g : BinaryCurveGeometry phi lam S slope c)
    (hp : p∈Icc (9/25:ℝ) lam) (hq : q∈Icc (0:ℝ) p)
    (hz : z∈Icc (391/500:ℝ) (7/8))
    (hpref : pref∈Icc (313/1000:ℝ) (9/25))
    (harea : binarySlackArea phi lam S pref≤epsArea)
    (hscore : scoreDefect phi lam pref≤epsScore)
    (hN : 0<denominator lam S p t)
    (hJ : 0≤betaNumerator lam p t)
    (hD0 : 0<etaNumerator lam S (9/25) t)
    (hD : 0≤etaNumerator lam S p t)
    (hbase : extendedBaseCore lam S (9/25) t z (primitiveDefect phi lam S z) (phi z)≤0)
    (hdefect : primitiveDefect phi lam S z∈Icc (0:ℝ) emax)
    (hcheck : extendedSelectedResidual lam S (9/25) p t q z emax
      (extendedSlackUpper lam S (phi 0) slope (527/2000) (1459/5000) q)
      (extendedRemainingUpper lam S (phi 0) slope (527/2000) (313/1000) pref
        (9/25) (309/1000) epsArea epsScore (z-p+q))≤0) :
    z+q-lam+extendedBeta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*
      packingK phi p q z+
      extendedEta lam p t (curvePrimitive phi p) (curvePrimitive phi (1-p))*phi z≤0 := by
  have hR := g.line_primitive p ⟨by linarith only [hp.1],by linarith only [hp.2,g.lambda_mem.2]⟩
  have hP := g.line_primitive (1-p) ⟨by linarith only [hp.2,g.lambda_mem.2],by linarith only [hp.1]⟩
  have hr : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hz.1,hp.2,g.lambda_mem.2,hq.1],by linarith only [hz.2,hq.2]⟩
  apply extended_high_of_core hR hP hN hJ
    (g.slackUpper_bound h ⟨hq.1,hq.2.trans hp.2⟩)
    (g.remainingUpper_bound h hpref harea hscore hr)
  apply extended_compare_nonpos hD0 hD hbase
  exact (extended_compare_le_selected hp.1 hdefect).trans hcheck

end OptimalG
