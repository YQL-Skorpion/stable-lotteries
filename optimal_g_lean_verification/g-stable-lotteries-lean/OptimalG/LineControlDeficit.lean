import OptimalG.Certificates.LineControlBounds
import OptimalG.FixedControlCubicDeficit

namespace OptimalG
open Set
namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The exact fixed control on the line gives both the middle scale estimate
and the cubic score-deficit bound used by mixed high-rank tests. -/
theorem lineControl_deficits {S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hcap : ∀ r∈Icc (391/500:ℝ) 1,curvePrimitive phi r≤Variational.quadratic lam r-S)
    (hcontrol : ∀ r∈Icc (391/500:ℝ) 1,phi r≤
      -Certificates.LineControl.theta lam S*(r-lam)-Certificates.LineControl.alpha lam S*
        (Variational.quadratic lam (r-9/25)-S-curvePrimitive phi r)) :
    (∀ r∈Icc (17/20:ℝ) (7/8),curvePrimitive phi r≤Variational.quadratic lam r-S-
      Certificates.LineControl.slope lam S*(r-Certificates.LineControl.crossing lam S)^2/2) ∧
    ∀ r∈Icc (391/500:ℝ) 1,
      let m:=Certificates.LineControl.slope lam S
      let alpha:=Certificates.LineControl.alpha lam S
      let v:=max (m*(r-Certificates.LineControl.crossing lam S)) 0
      v+alpha/(2*m)*v^2+alpha^2/(6*m^2)*v^3≤lam-r-phi r := by
  let m:=Certificates.LineControl.slope lam S
  let alpha:=Certificates.LineControl.alpha lam S
  let c:=Certificates.LineControl.crossing lam S
  let D : ℝ→ℝ := fun r=>Variational.quadratic lam r-S-curvePrimitive phi r
  have hunit : (0:ℝ)∈Icc 0 1 := by constructor <;> norm_num
  have hden := Certificates.LineControl.denominator_pos hL hS
  have hnum := Certificates.LineControl.slopeNumerator_pos hL hS
  have hm : 0<m := by
    have hh := Certificates.LineControl.slopeLo_pos hL hS hunit
    dsimp [m]
    linarith only [hh]
  have halpha : 0≤alpha := (Certificates.LineControl.alphaLo_pos hL hS hunit).le
  have hc : c∈Icc (391/500:ℝ) 1 := by
    have hl := Certificates.LineControl.crossLo_pos hL hS hunit
    have hu := Certificates.LineControl.crossHi_pos hL hS hunit
    dsimp [c]
    constructor <;> linarith only [hl,hu]
  have hD : ∀ r∈Icc (391/500:ℝ) 1,0≤D r := by
    intro r hr
    exact sub_nonneg.mpr (hcap r hr)
  have hE : ∀ r∈Icc (391/500:ℝ) 1,0≤lam-r-phi r := by
    intro r hr
    have hh := h.ceiling r ⟨by linarith only [hr.1],hr.2⟩
    linarith only [hh]
  have hcont : ContinuousOn D (Icc (391/500:ℝ) 1) := by
    have hh := h.primitive_continuous.mono
      (show Icc (391/500:ℝ) 1⊆Icc 0 1 from Icc_subset_Icc (by norm_num) le_rfl)
    dsimp [D,Variational.quadratic]
    fun_prop
  have hd (r : ℝ) (hr : r∈Ioo (391/500:ℝ) 1) :
      HasDerivAt D (lam-r-phi r) r := by
    have hh := h.primitive_hasDerivAt ⟨by linarith only [hr.1],hr.2⟩
    exact ((Variational.quadratic_hasDerivAt lam r).sub_const S).sub hh
  have hfield (r : ℝ) (hr : r∈Icc (391/500:ℝ) 1) : m*(r-c)+alpha*D r≤lam-r-phi r := by
    have hh := hcontrol r hr
    have he := control_deficit_identity lam S (9/25)
      (Certificates.LineControl.theta lam S) alpha (curvePrimitive phi r) r
    have hmId := Certificates.LineControl.slope_identity hden.ne'
    have hcId := Certificates.LineControl.crossing_identity hden.ne' hnum.ne'
    change m=Certificates.LineControl.theta lam S-1+alpha*(9/25) at hmId
    change m*(c-lam)=alpha*(9/25)^2/2 at hcId
    change lam-r-(-Certificates.LineControl.theta lam S*(r-lam)-alpha*
      (Variational.quadratic lam (r-9/25)-S-curvePrimitive phi r))=
      (Certificates.LineControl.theta lam S-1+alpha*(9/25))*(r-lam)-alpha*(9/25)^2/2+alpha*D r at he
    rw [←hmId] at he
    nlinarith only [hh,he,hcId]
  have hh := positive_part_deficit_growth_cubic hc hm halpha hcont hd hD hE hfield
  refine ⟨?_,hh.2⟩
  intro r hr
  have hcross := Certificates.LineControl.crossHi_pos hL hS hunit
  have hcr : c≤r := by dsimp [c]; linarith only [hcross,hr.1]
  have hp := hh.1 r ⟨hcr,by linarith only [hr.2]⟩
  have hextra : 0≤(alpha*m/6)*(r-c)^3 := by
    exact mul_nonneg (div_nonneg (mul_nonneg halpha hm.le) (by norm_num))
      (pow_nonneg (sub_nonneg.mpr hcr) 3)
  dsimp [D] at hp
  change curvePrimitive phi r≤Variational.quadratic lam r-S-m*(r-c)^2/2
  nlinarith only [hp,hextra]

end VerifierCurve
end OptimalG
