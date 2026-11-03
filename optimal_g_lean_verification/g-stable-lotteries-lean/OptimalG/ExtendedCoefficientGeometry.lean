import OptimalG.Certificates.ExtendedScalarExpressions

/-! Analytic transport for the final C.4 coefficient family. Polynomial sign
checks are separated from the derivative and supporting-line arguments. -/
namespace OptimalG
open Set Variational Certificates.ExtendedScalarExpressions

theorem extendedEta_eq_of_system {lam p t R P beta eta : ℝ}
    (hN : extendedDenom lam p t R P≠0)
    (hfirst : beta*P+eta*(lam-t)=2*lam-t)
    (hsecond : beta*R-eta*(lam-p)=2*p-lam) :
    extendedEta lam p t R P=eta := by
  have h1 := congrArg (fun x : ℝ => x*R) hfirst
  have h2 := congrArg (fun x : ℝ => x*P) hsecond
  unfold extendedEta
  apply (div_eq_iff hN).mpr
  unfold extendedDenom
  nlinarith only [h1,h2]

theorem extendedBeta_eq_of_system {lam p t R P beta eta : ℝ}
    (hN : extendedDenom lam p t R P≠0)
    (hfirst : beta*P+eta*(lam-t)=2*lam-t)
    (hsecond : beta*R-eta*(lam-p)=2*p-lam) :
    extendedBeta lam p t R P=beta := by
  have h1 := congrArg (fun x : ℝ => x*(lam-p)) hfirst
  have h2 := congrArg (fun x : ℝ => x*(lam-t)) hsecond
  unfold extendedBeta
  apply (div_eq_iff hN).mpr
  unfold extendedDenom
  nlinarith only [h1,h2]

theorem extended_scalar_denominator_pos {lam S p t : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (9/25:ℝ) lam) (ht : t∈Icc (1529/5000:ℝ) (9/25)) :
    0<denominator lam S p t := by
  have hprod := mul_nonneg (sub_nonneg.mpr hp.1)
    (show 0≤lam-(p+9/25)/2 by linarith only [hp.2,hL.1])
  have hR : 0<quadratic lam p-S := by
    unfold quadratic
    nlinarith only [hprod,hL.1,hS.2]
  have hr : (43/100:ℝ)≤1-p := by linarith only [hp.2,hL.2]
  have hslope : (6/25:ℝ)≤lam-(1-p)/2 := by linarith only [hp.1,hL.1]
  have hprodP := mul_le_mul hr hslope (by norm_num : (0:ℝ)≤6/25)
    (by linarith only [hr] : 0≤1-p)
  have hP : 0≤quadratic lam (1-p)-S := by
    unfold quadratic
    nlinarith only [hprodP,hS.2]
  exact extendedDenom_pos (by linarith only [ht.2,hL.1]) hp.2 hR hP

theorem extended_scalar_eta_hasDerivAt {lam S t p : ℝ}
    (hN : denominator lam S p t≠0) :
    HasDerivAt (fun r => extendedEta lam r t (quadratic lam r-S) (quadratic lam (1-r)-S))
      (-etaDecrease lam S p t/(denominator lam S p t)^2) p := by
  have hR := (quadratic_hasDerivAt lam p).sub_const S
  have hP : HasDerivAt (fun r => quadratic lam (1-r)-S) (1-p-lam) p := by
    convert! ((quadratic_hasDerivAt lam (1-p)).comp p
      ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p))).sub_const S using 1 <;>
      first | rfl | (simp only [id_eq,zero_sub]; ring)
  have hNd : HasDerivAt (fun r => denominator lam S r t) (denominatorDerivative lam S p t) p := by
    convert! (hR.const_mul (lam-t)).add
      (((hasDerivAt_const p lam).sub (hasDerivAt_id p)).mul hP) using 1 <;>
      first | rfl | (simp only [denominatorDerivative,Pi.sub_apply,id_eq,zero_sub]; ring)
  have hDd : HasDerivAt (fun r => etaNumerator lam S r t) (etaNumeratorDerivative lam S p t) p := by
    convert! (hR.const_mul (2*lam-t)).sub
      ((((hasDerivAt_id p).const_mul 2).sub_const lam).mul hP) using 1 <;>
      first | rfl | (simp only [etaNumeratorDerivative,Pi.sub_apply,id_eq,mul_one]; ring)
  change HasDerivAt (fun r => etaNumerator lam S r t/denominator lam S r t) _ p
  convert! hDd.div hNd hN using 1
  unfold etaDecrease
  ring

theorem extended_scalar_eta_antitone {lam S t a b : ℝ}
    (hN : ∀ p∈Icc a b,0<denominator lam S p t)
    (hpoly : ∀ p∈Icc a b,0≤etaDecrease lam S p t) :
    AntitoneOn (fun p => extendedEta lam p t (quadratic lam p-S) (quadratic lam (1-p)-S))
      (Icc a b) := by
  have hd (p : ℝ) (hp : p∈Icc a b) := extended_scalar_eta_hasDerivAt (hN p hp).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (fun p hp => (hd p hp).continuousAt.continuousWithinAt)
    (f':=fun p => -etaDecrease lam S p t/(denominator lam S p t)^2)
  · intro p hp
    exact (hd p (interior_subset hp)).hasDerivWithinAt
  · intro p hp
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hpoly p (interior_subset hp))) (sq_nonneg _)

theorem extended_mass_slack_of_polynomial {lam S p t : ℝ}
    (hN : 0<denominator lam S p t) (hpoly : 0≤massSlack lam S p t) :
    extendedEta lam p t (quadratic lam p-S) (quadratic lam (1-p)-S)≤
      1+extendedBeta lam p t (quadratic lam p-S) (quadratic lam (1-p)-S)*p := by
  rw [eta_eq,beta_eq]
  have hn : etaNumerator lam S p t≤denominator lam S p t+betaNumerator lam p t*p := by
    unfold massSlack at hpoly
    linarith only [hpoly]
  calc
    _≤(denominator lam S p t+betaNumerator lam p t*p)/denominator lam S p t :=
      div_le_div_of_nonneg_right hn hN.le
    _=1+betaNumerator lam p t/denominator lam S p t*p := by
      field_simp [hN.ne']

theorem extended_split_gap_of_polynomial {lam S p t z0 : ℝ}
    (hN : 0<denominator lam S p t)
    (hpoly : denominator lam S p t≤betaNumerator lam p t*
      (Certificates.SmallMassExpressions.initial lam S-lam+z0-p)) :
    1≤extendedBeta lam p t (quadratic lam p-S) (quadratic lam (1-p)-S)*
      (Certificates.SmallMassExpressions.initial lam S-lam+z0-p) := by
  rw [beta_eq,div_mul_eq_mul_div,le_div_iff₀ hN]
  simpa only [one_mul] using hpoly

end OptimalG
