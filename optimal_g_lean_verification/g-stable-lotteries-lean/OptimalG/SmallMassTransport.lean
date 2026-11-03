import OptimalG.SupportingMinimumRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Finite supporting-coefficient comparison and the C.4 transport rate.
The only numerical inputs to the rate test are its four rectangle corners.
No derivative of a minimizing rank, or Danskin theorem, is assumed. -/
namespace OptimalG
open Set

/-- Multiplication by a nonpositive high-rank score turns the finite infimum
comparison into a lower bound for the change of the transported expression. -/
theorem supportMinimum_weighted_transport {phi m F : ℝ → ℝ} {lam A w : ℝ} {D : Set ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (htarget : ∀ p ∈ D, lam<m p) (hanti : AntitoneOn m D) (hw : w≤0)
    (hA : ∀ p ∈ D, ∀ x ∈ Ico 0 lam,
      supportMinimum phi lam (m p)=(m p-x)/phi x → phi x≤A)
    (hadjusted : MonotoneOn (fun p => F p+(m p/A)*w) D) :
    MonotoneOn (fun p => F p+supportMinimum phi lam (m p)*w) D := by
  intro a ha b hb hab
  obtain ⟨_,x,hx,hmin,_⟩ := supportMinimum_attained hlam hc hz hp (htarget a ha)
  have hh := supportMinimum_decrease_bound hlam hc hz hp (htarget b hb)
    (hanti ha hb hab) hx hmin (hA a ha x hx hmin)
  have hmul := mul_le_mul_of_nonpos_right hh hw
  have hm := hadjusted ha hb hab
  rw [sub_div] at hmul
  nlinarith

noncomputable def smallMassPsi (J phi beta m : ℝ → ℝ) (lam p z : ℝ) : ℝ :=
  z-lam+beta p*(J (z-p)-J z)+supportMinimum phi lam (m p)*phi z

noncomputable def smallMassAdjusted (J phi beta m : ℝ → ℝ) (lam A p z : ℝ) : ℝ :=
  z-lam+beta p*(J (z-p)-J z)+(m p/A)*phi z

/-- The lower rate from C.4, written without derivative notation. -/
noncomputable def smallMassRate (lam zminus p beta b a z e : ℝ) : ℝ :=
  (a+b*p+beta)*(z-lam)-b*p^2/2-beta*p+(a+b*(z-zminus)/2)*e

private theorem affine_nonneg_between {s t x a b : ℝ} (hx : x ∈ Icc s t)
    (hs : 0≤b+a*s) (ht : 0≤b+a*t) : 0≤b+a*x := by
  by_cases ha : 0≤a
  · have hh := mul_le_mul_of_nonneg_left hx.1 ha
    linarith
  · have hh := mul_le_mul_of_nonpos_left hx.2 (le_of_not_ge ha)
    linarith

/-- Four corner inequalities suffice because the rate is affine in each of z,e. -/
theorem smallMassRate_nonneg {lam zminus p beta b a z e : ℝ}
    (hz : z ∈ Icc zminus 1) (he : e ∈ Icc 0 lam)
    (h00 : 0≤smallMassRate lam zminus p beta b a zminus 0)
    (h01 : 0≤smallMassRate lam zminus p beta b a zminus lam)
    (h10 : 0≤smallMassRate lam zminus p beta b a 1 0)
    (h11 : 0≤smallMassRate lam zminus p beta b a 1 lam) :
    0≤smallMassRate lam zminus p beta b a z e := by
  have hleft : 0≤smallMassRate lam zminus p beta b a zminus e := by
    apply affine_nonneg_between he
      (a:=a+b*(zminus-zminus)/2)
      (b:=(a+b*p+beta)*(zminus-lam)-b*p^2/2-beta*p)
    · simpa only [smallMassRate] using h00
    · simpa only [smallMassRate] using h01
  have hright : 0≤smallMassRate lam zminus p beta b a 1 e := by
    apply affine_nonneg_between he
      (a:=a+b*(1-zminus)/2)
      (b:=(a+b*p+beta)*(1-lam)-b*p^2/2-beta*p)
    · simpa only [smallMassRate] using h10
    · simpa only [smallMassRate] using h11
  let slope := a+b*p+beta+b*e/2
  let intercept := -(a+b*p+beta)*lam-b*p^2/2-beta*p+a*e-b*zminus*e/2
  have hidentity (u : ℝ) : smallMassRate lam zminus p beta b a u e=intercept+slope*u := by
    dsimp [smallMassRate,slope,intercept]
    ring
  rw [hidentity] at hleft hright ⊢
  exact affine_nonneg_between hz hleft hright

/-- Algebraic reduction of the smooth adjusted derivative to the four-corner rate.
The primitive cap, score ceiling, and deficit-area bound are explicit premises. -/
theorem smallMassRate_le_derivative {lam zminus p beta b a z e d K lowScore highScore : ℝ}
    (hbeta : 0≤beta) (hb : b≤0)
    (hK : K≤p*(z-lam)-p^2/2+d)
    (hlow : lowScore≤lam-z+p) (hhigh : highScore=lam-z-e)
    (hd : d≤(z-zminus)*e/2) :
    smallMassRate lam zminus p beta b a z e≤b*K-beta*lowScore-a*highScore := by
  have h1 := mul_le_mul_of_nonpos_left hK hb
  have h2 := mul_le_mul_of_nonneg_left hlow hbeta
  have h3 := mul_le_mul_of_nonpos_left hd hb
  rw [hhigh]
  dsimp [smallMassRate]
  nlinarith

theorem smallMassAdjusted_hasDerivAt {J phi beta m : ℝ → ℝ} {lam A p z b dm : ℝ}
    (hbeta : HasDerivAt beta b p) (hm : HasDerivAt m dm p)
    (hJ : HasDerivAt J (phi (z-p)) (z-p)) :
    HasDerivAt (fun p => smallMassAdjusted J phi beta m lam A p z)
      (b*(J (z-p)-J z)-beta p*phi (z-p)+(dm/A)*phi z) p := by
  have hshift := hJ.comp p ((hasDerivAt_const p z).sub (hasDerivAt_id p))
  have hprod := hbeta.mul (hshift.sub_const (J z))
  have hsum := (hprod.const_add (z-lam)).add ((hm.div_const A).mul_const (phi z))
  convert! hsum using 1 <;> (try dsimp [smallMassAdjusted,Function.comp_def]) <;> ring

/-- Once the numerical corner tests imply a nonnegative smooth derivative,
the finite support comparison transports any stored right-endpoint bound. -/
theorem smallMassPsi_nonpos_of_adjusted_rate {J phi beta m db dm : ℝ → ℝ}
    {lam A left right z : ℝ}
    (hlam : 0<lam) (hphi : ContinuousOn phi (Icc 0 lam))
    (hzero : phi lam=0) (hpositive : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hlr : left≤right)
    (htarget : ∀ p ∈ Icc left right, lam<m p)
    (hanti : AntitoneOn m (Icc left right)) (hhigh : phi z≤0)
    (hA : ∀ p ∈ Icc left right, ∀ x ∈ Ico 0 lam,
      supportMinimum phi lam (m p)=(m p-x)/phi x → phi x≤A)
    (hbetac : ContinuousOn beta (Icc left right)) (hmc : ContinuousOn m (Icc left right))
    (hJc : ContinuousOn (fun p => J (z-p)) (Icc left right))
    (hbetad : ∀ p ∈ Ioo left right, HasDerivAt beta (db p) p)
    (hmd : ∀ p ∈ Ioo left right, HasDerivAt m (dm p) p)
    (hJd : ∀ p ∈ Ioo left right, HasDerivAt J (phi (z-p)) (z-p))
    (hrate : ∀ p ∈ Ioo left right,
      0≤db p*(J (z-p)-J z)-beta p*phi (z-p)+(dm p/A)*phi z)
    (hend : smallMassPsi J phi beta m lam right z≤0) :
    ∀ p ∈ Icc left right, smallMassPsi J phi beta m lam p z≤0 := by
  have hadjcont : ContinuousOn (fun p => smallMassAdjusted J phi beta m lam A p z)
      (Icc left right) :=
    (continuousOn_const.add (hbetac.mul (hJc.sub continuousOn_const))).add
      ((hmc.div_const A).mul continuousOn_const)
  have hadj : MonotoneOn (fun p => smallMassAdjusted J phi beta m lam A p z)
      (Icc left right) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc left right) hadjcont
      (f':=fun p => db p*(J (z-p)-J z)-beta p*phi (z-p)+(dm p/A)*phi z)
    · intro p hp
      have hp' : p ∈ Ioo left right := by simpa using hp
      exact (smallMassAdjusted_hasDerivAt (hbetad p hp') (hmd p hp') (hJd p hp')).hasDerivWithinAt
    · intro p hp
      exact hrate p (by simpa using hp)
  have hmono := supportMinimum_weighted_transport
    (F:=fun p => z-lam+beta p*(J (z-p)-J z))
    hlam hphi hzero hpositive htarget hanti hhigh hA hadj
  intro p hp
  exact (hmono hp ⟨hlr,le_rfl⟩ hp.2).trans hend

end OptimalG
