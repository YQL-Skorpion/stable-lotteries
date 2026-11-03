import OptimalG.Certificates.CubicProfile
import OptimalG.Certificates.TransportSegments
import OptimalG.Certificates.RationalCalculus

/-! Exact reference data and its scalar gauge. The constructor is transparent;
all advertised endpoint and derivative identities are decided over rationals. -/
namespace OptimalG.Certificates.Transport

structure ReferenceData where
  lam : ℚ
  slack : ℚ
  leftContact : ℚ
  rightContact : ℚ
  terminalQ : ℚ
  pieces : List CubicPiece
  gauge : RationalPolynomial
  gaugeDerivative : RationalPolynomial
  controls : List ReferenceNode

namespace ReferenceData

def gaugeCheck (d : ReferenceData) : Bool :=
  decide (d.leftContact<d.rightContact ∧ d.leftContact<1 ∧
    d.gauge.evalQ 0 = -d.lam/(1-d.leftContact) ∧
    d.gauge.evalQ 1 = -1 ∧
    d.gaugeDerivative.evalQ 0 = -d.lam/(1-d.leftContact)^2 ∧
    d.gaugeDerivative.evalQ 1 = 0) &&
  RationalPolynomial.eqCheck d.gauge.derivative
    (RationalPolynomial.scale (d.rightContact-d.leftContact) d.gaugeDerivative)

noncomputable def centralGauge (d : ReferenceData) (r : ℝ) : ℝ :=
  d.gauge.eval ((r-d.leftContact)/((d.rightContact:ℝ)-d.leftContact))

noncomputable def centralGaugeDerivative (d : ReferenceData) (r : ℝ) : ℝ :=
  d.gaugeDerivative.eval ((r-d.leftContact)/((d.rightContact:ℝ)-d.leftContact))

theorem gauge_derivative {d : ReferenceData} (hc : d.gaugeCheck=true) (r : ℝ) :
    HasDerivAt d.centralGauge (d.centralGaugeDerivative r) r := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hr := of_decide_eq_true hh.1
  have hne : d.rightContact-d.leftContact≠0 := sub_ne_zero.mpr (ne_of_gt hr.1)
  change HasDerivAt (fun x:ℝ => d.gauge.eval ((x-d.leftContact)/((d.rightContact:ℝ)-d.leftContact)))
    (d.centralGaugeDerivative r) r
  simpa only [centralGaugeDerivative,Rat.cast_sub] using
    RationalPolynomial.hasDerivAt_affine_of_check hh.2 hne (d.leftContact:ℝ) r

theorem gauge_endpoints {d : ReferenceData} (hc : d.gaugeCheck=true) :
    d.centralGauge d.leftContact= -(d.lam:ℝ)/(1-d.leftContact) ∧
    d.centralGauge d.rightContact= -1 ∧
    d.centralGaugeDerivative d.leftContact= -(d.lam:ℝ)/(1-d.leftContact)^2 ∧
    d.centralGaugeDerivative d.rightContact=0 := by
  have hr := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hne : (d.rightContact:ℝ)-d.leftContact≠0 := by exact_mod_cast sub_ne_zero.mpr (ne_of_gt hr.1)
  have h0 := congrArg (fun q:ℚ => (q:ℝ)) hr.2.2.1
  have h1 := congrArg (fun q:ℚ => (q:ℝ)) hr.2.2.2.1
  have hd0 := congrArg (fun q:ℚ => (q:ℝ)) hr.2.2.2.2.1
  have hd1 := congrArg (fun q:ℚ => (q:ℝ)) hr.2.2.2.2.2
  norm_num only [RationalPolynomial.cast_evalQ,Rat.cast_div,Rat.cast_neg,Rat.cast_sub,
    Rat.cast_one,Rat.cast_zero,Rat.cast_pow] at h0 h1 hd0 hd1
  simpa only [centralGauge,centralGaugeDerivative,sub_self,zero_div,div_self hne] using
    And.intro h0 (And.intro h1 (And.intro hd0 hd1))

end ReferenceData
end OptimalG.Certificates.Transport
