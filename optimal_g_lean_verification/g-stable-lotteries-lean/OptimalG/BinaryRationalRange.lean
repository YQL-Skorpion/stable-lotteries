import OptimalG.BinaryCurveGeometry
import OptimalG.RationalContactLocalization
import OptimalG.RationalStationaryRegularity

/-! The entire rational stationary range is built from the true contact and
finite scalar curvature/endpoint residuals. -/
namespace OptimalG
open Set MeasureTheory Filter Variational
open scoped Topology

/-- The rational level equation is the actual stationary numerator equation. -/
theorem rationalStationary_actual_root {phi : ℝ → ℝ} {lam S p q : ℝ}
    (hqJ : curvePrimitive phi q=cap lam S q) (hqScore : phi q=capScore lam S q)
    (hshiftJ : curvePrimitive phi (q+1-p)=quadratic lam (q+1-p)-S)
    (hshiftScore : phi (q+1-p)=lam-(q+1-p))
    (hmatch : stationaryLevel lam S q=(1-p)^2) :
    binaryStationaryNumerator phi lam p q=0 := by
  unfold binaryStationaryNumerator
  rw [hqJ,hqScore,hshiftJ,hshiftScore]
  unfold stationaryLevel capSlack capDeficit at hmatch
  unfold quadratic at *
  nlinarith only [hmatch]

namespace BinaryCurveGeometry
variable {phi : ℝ → ℝ} {lam S slope c : ℝ} (g : BinaryCurveGeometry phi lam S slope c)
include g

/-- From the actual contact through mass .9125, the constructed rational
stationary branch is globally controlling and lies below the actual tail. -/
theorem binary_after_contact (h : VerifierCurve phi lam)
    {z qs Y H : ℝ}
    (hc : ConcaveOn ℝ (Icc lam 1) phi)
    (hS : S ∈ Icc (0:ℝ) (3/100:ℝ))
    (hz : z ∈ Icc (849/1000:ℝ) (7/8:ℝ))
    (hqs : qs ∈ Icc (527/2000:ℝ) (691/2500:ℝ))
    (hmatch : stationaryLevel lam S qs=(1-z)^2)
    (hvalue : curvePrimitive phi z=z*((1-z)-capSlack lam S qs))
    (hslope : phi z=1-2*z-capSlack lam S qs+z*(1-z)/(lam-qs))
    (htail : ∀ p ∈ Icc z 1,phi p=tailScore z Y H p)
    (hend : stationaryLevel lam S (1459/5000)≤(7/80:ℝ)^2)
    (hshift : ∀ p ∈ Icc z (73/80:ℝ),∀ r ∈ Icc qs (1459/5000:ℝ),
      stationaryLevel lam S r=(1-p)^2 → 7189/20000≤r+1-p)
    (hzero : ∀ p ∈ Icc z (73/80:ℝ),∀ r ∈ Icc qs (1459/5000:ℝ),
      stationaryLevel lam S r=(1-p)^2 →
      (phi 0)*(1-p)+slope*(1-p)^2/2≤lam*((1-p)-capSlack lam S r))
    (hcurvature : ∀ p ∈ Ioo z (73/80:ℝ),∀ r ∈ Icc qs (1459/5000:ℝ),
      stationaryLevel lam S r=(1-p)^2 → stationaryBarrierCurvature lam S p r≤tailSlope z Y H p) :
    ∀ p ∈ Icc z (73/80:ℝ),∀ q ∈ Icc (0:ℝ) p,normalizedBinaryTest phi p q≤lam := by
  have hl : lam ∈ Icc (11/20:ℝ) (3/5:ℝ) :=
    ⟨by linarith only [g.lambda_mem.1],by linarith only [g.lambda_mem.2]⟩
  have hqv : qs≤1459/5000 := by linarith only [hqs.2]
  have hvl : (1459/5000:ℝ)<lam := by linarith only [g.lambda_mem.1]
  have hzb : z≤73/80 := by linarith only [hz.2]
  have hcurv (r : ℝ) (hr : r ∈ Icc qs (1459/5000:ℝ)) :
      (2/5:ℝ)≤2*(lam-r)*capSlopeGap lam S r :=
    capStationarySlope_lower hl hS (by linarith only [hr.2])
  have hgap (r : ℝ) (hr : r ∈ Icc qs (1459/5000:ℝ)) : 0<capSlopeGap lam S r := by
    have hh := capSlopeGap_lower (r:=r) hl.2 hS (by linarith only [hr.2])
    linarith only [hh]
  obtain ⟨r,hr,hrlip,hrd⟩ := exists_rational_stationary_branch hqv
    (by norm_num : (1459/5000:ℝ)<1) hvl (by linarith only [hz.1] : 0≤z)
    hzb (by norm_num : (73/80:ℝ)≤1) (by norm_num : (0:ℝ)<2/5) hcurv hmatch.ge
    (by convert hend using 1 <;> norm_num)
  have hrz : r z=qs := by
    have hanti := stationaryLevel_strictAntiOn hvl (by norm_num : (1459/5000:ℝ)<1) hgap
    exact hanti.injOn (hr z ⟨le_rfl,hzb⟩).1 ⟨le_rfl,hqv⟩
      ((hr z ⟨le_rfl,hzb⟩).2.trans hmatch.symm)
  have hTvalue : stationaryBarrier lam S r z≤curvePrimitive phi z := by
    unfold stationaryBarrier
    rw [hrz,hvalue]
  have hTslope : stationaryBarrierSlope lam S r z≤phi z := by
    unfold stationaryBarrierSlope
    rw [hrz,hslope]
  have hcurvatureAE : ∀ᵐ p ∂volume.restrict (Icc z (73/80:ℝ)),
      stationaryBarrierCurvature lam S p (r p)≤deriv phi p := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    have he : phi =ᶠ[𝓝 p] tailScore z Y H := by
      filter_upwards [Ioo_mem_nhds hp.1 (show p<1 by linarith only [hp.2])] with t ht
      exact htail t ⟨ht.1.le,ht.2.le⟩
    rw [((tailScore_hasDerivAt z Y H p).congr_of_eventuallyEq he).deriv]
    exact hcurvature p hp (r p) (hr p ⟨hp.1.le,hp.2.le⟩).1 (hr p ⟨hp.1.le,hp.2.le⟩).2
  have hbound := rational_stationary_barrier_comparison hzb
    (by linarith only [g.lambda_mem.2,hz.1] : lam<z) (by norm_num : (73/80:ℝ)<1)
    hrlip (fun p hp => (hr p hp).1) (by norm_num : (1459/5000:ℝ)<1) hvl hgap
    (fun p hp => (hr p hp).2)
    (h.primitive_continuous.mono (Icc_subset_Icc (by linarith only [hz.1]) (by norm_num))) hc
    (fun p hp => h.primitive_hasDerivAt ⟨by linarith only [hp.1,hz.1],by linarith only [hp.2]⟩)
    hcurvatureAE hTvalue hTslope
  intro p hp
  have hpr := (hr p hp).1
  have hlevel := (hr p hp).2
  have hrhead : (527/2000:ℝ)≤r p := hqs.1.trans hpr.1
  have hrc : r p≤c := hpr.2.trans g.contact_mem.1
  have hrl : r p<lam := hpr.2.trans_lt hvl
  have hrshift := hshift p hp (r p) hpr hlevel
  have hshiftMem : r p+1-p ∈ Icc (7189/20000:ℝ) (31/40:ℝ) :=
    ⟨hrshift,by linarith only [hpr.2,hp.1,hz.1]⟩
  have hroot := rationalStationary_actual_root (g.cap_primitive (r p) ⟨hrhead,hrc⟩)
    (g.cap_score (r p) ⟨hrhead,hrc⟩) (g.line_primitive _ hshiftMem) (g.line_score _ hshiftMem) hlevel
  have hratio : binaryRatio phi lam p (r p)=(1-p)-capSlack lam S (r p) := by
    rw [h.binaryRatio_eq_deficit hrl hroot (g.line_score _ hshiftMem),g.cap_score (r p) ⟨hrhead,hrc⟩]
    rfl
  have hvalueP := hbound p hp
  change p*((1-p)-capSlack lam S (r p))≤curvePrimitive phi p at hvalueP
  exact g.binary_of_stationary_value h hc
    ⟨by linarith only [hp.1,hz.1],hp.2⟩
    ⟨by linarith only [hpr.1,hqs.1],hrl⟩ hrshift hroot hratio
    (hzero p hp (r p) hpr hlevel) hvalueP

end BinaryCurveGeometry
end OptimalG
