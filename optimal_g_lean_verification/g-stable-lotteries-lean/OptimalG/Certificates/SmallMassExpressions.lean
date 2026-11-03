import OptimalG.SmallMassCoefficients
import OptimalG.PolynomialCompletion
import OptimalG.VariationalCapSlope
import OptimalG.BinarySmallCentral

/-! Exact rational expressions underlying the C.4 finite checks, linked to
the actual affine head of a verifier curve. -/
namespace OptimalG.Certificates.SmallMassExpressions
open Set

noncomputable def initial (lam S : ℝ) : ℝ :=
  headInitial (527/2000) (Variational.cap lam S (527/2000))
    (Variational.capScore lam S (527/2000))
noncomputable def slope (lam S : ℝ) : ℝ :=
  headSlope (527/2000) (Variational.cap lam S (527/2000))
    (Variational.capScore lam S (527/2000))
noncomputable def score (lam S r : ℝ) : ℝ := initial lam S+slope lam S*r
noncomputable def primitive (lam S r : ℝ) : ℝ := initial lam S*r+slope lam S*r^2/2
noncomputable def denominator (lam S p : ℝ) : ℝ :=
  smallMassDenominator (primitive lam S) lam S p
noncomputable def beta (lam S p : ℝ) : ℝ := smallMassBeta (primitive lam S) lam S p
noncomputable def target (lam S p : ℝ) : ℝ := smallMassTarget (primitive lam S) lam S p
noncomputable def betaDerivative (lam S p : ℝ) : ℝ :=
  smallMassBetaDerivative (primitive lam S) (score lam S) lam S p
noncomputable def targetDerivative (lam S p : ℝ) : ℝ :=
  smallMassTargetDerivative (primitive lam S) (score lam S) lam S p
noncomputable def cap28 (lam S : ℝ) : ℝ := Variational.capScore lam S (7/25)
noncomputable def cap2918 (lam S : ℝ) : ℝ := Variational.capScore lam S (1459/5000)
noncomputable def etaOne (lam S p : ℝ) : ℝ := 1+beta lam S p*p
noncomputable def etaTwo (lam S p : ℝ) : ℝ := 1+(target lam S p-lam)/cap28 lam S
noncomputable def etaWitness (lam S p : ℝ) : ℝ := (target lam S p-1459/5000)/cap2918 lam S
noncomputable def rateSlope (lam S p A : ℝ) : ℝ :=
  -targetDerivative lam S p/A+betaDerivative lam S p*p+beta lam S p
noncomputable def rateLeft (lam S p A : ℝ) : ℝ :=
  (391/500-lam)*rateSlope lam S p A-betaDerivative lam S p*p^2/2-beta lam S p*p
noncomputable def rateRight (lam S p A : ℝ) : ℝ :=
  -targetDerivative lam S p/A+
    betaDerivative lam S p*((1-lam)*p-p^2/2+lam*(109/1000))+beta lam S p*(1-lam-p)

theorem affine_head_agrees {phi : ℝ→ℝ} {lam S : ℝ} (h : VerifierCurve phi lam)
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=score lam S r) :
    ∀ p∈Icc (0:ℝ) (527/2000),curvePrimitive phi p=primitive lam S p := by
  have hzero : phi 0=initial lam S := by simpa [score] using hhead 0 ⟨le_rfl,by norm_num⟩
  intro p hp
  have hh := h.affine_head_primitive (slope:=slope lam S)
    (fun r hr => by rw [hhead r hr,hzero]; rfl) hp
  simpa only [hzero,primitive] using hh

theorem coefficients_agree {phi : ℝ→ℝ} {lam S p : ℝ}
    (hJ : curvePrimitive phi p=primitive lam S p) (hphi : phi p=score lam S p) :
    smallMassDenominator (curvePrimitive phi) lam S p=denominator lam S p ∧
    smallMassBeta (curvePrimitive phi) lam S p=beta lam S p ∧
    smallMassTarget (curvePrimitive phi) lam S p=target lam S p ∧
    smallMassBetaDerivative (curvePrimitive phi) phi lam S p=betaDerivative lam S p ∧
    smallMassTargetDerivative (curvePrimitive phi) phi lam S p=targetDerivative lam S p := by
  simp only [denominator,beta,target,betaDerivative,targetDerivative,
    smallMassDenominator,smallMassBeta,smallMassTarget,smallMassBetaDerivative,
    smallMassTargetDerivative,hJ,hphi,and_self]

theorem rateLeft_eq (lam S p A : ℝ) : rateLeft lam S p A=
    smallMassRate lam (391/500) p (beta lam S p) (betaDerivative lam S p)
      (-targetDerivative lam S p/A) (391/500) 0 := by
  unfold rateLeft rateSlope smallMassRate
  ring

theorem rateRight_eq (lam S p A : ℝ) : rateRight lam S p A=
    smallMassRate lam (391/500) p (beta lam S p) (betaDerivative lam S p)
      (-targetDerivative lam S p/A) 1 lam := by
  unfold rateRight smallMassRate
  ring

end OptimalG.Certificates.SmallMassExpressions
