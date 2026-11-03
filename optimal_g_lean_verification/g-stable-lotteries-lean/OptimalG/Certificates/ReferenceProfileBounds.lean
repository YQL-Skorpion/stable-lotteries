import OptimalG.Certificates.ReferenceFlowExpressions
import OptimalG.Certificates.IntegerEnclosures
import OptimalG.Certificates.CapSupport

/-! Exact centered-polynomial and cap-endpoint enclosures for reference data. -/
namespace OptimalG.Certificates
open Set

def centeredPolynomialCheck (s k : ℕ) (p : RationalPolynomial) (lo hi : ℚ)
    (out : IntegerInterval) : Bool :=
  (RatExpr.polynomial (p.compose [(lo+hi)/2,(hi-lo)/2]) (.var (0:Fin 1))).enclosureRefinedCheck s k (fun _ => ⟨-(s:ℤ),s⟩) out

theorem centeredPolynomialCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (p : RationalPolynomial) (lo hi : ℚ) (out : IntegerInterval)
    (hc : centeredPolynomialCheck s k p lo hi out=true) (horder : lo<hi)
    {x : ℝ} (hx : x∈Icc (lo:ℝ) hi) : out.Contains s (p.eval x) := by
  let t := (2*x-(lo:ℝ)-hi)/((hi:ℝ)-lo)
  have hd : (0:ℝ)<(hi:ℝ)-lo := by exact_mod_cast sub_pos.mpr horder
  have hdn : (hi:ℝ)-(lo:ℝ)≠0 := ne_of_gt hd
  have ht : -(1:ℝ)≤t ∧ t≤1 := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hx.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hx.2]
  have hb : ∀ i : Fin 1,(⟨-(s:ℤ),(s:ℤ)⟩:IntegerInterval).Contains s t := by
    intro i
    constructor
    · simpa using mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg s)
    · simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg s)
  have h := RatExpr.enclosureRefinedCheck_sound hs hk
    (RatExpr.polynomial (p.compose [(lo+hi)/2,(hi-lo)/2]) (.var (0:Fin 1)))
    (fun _ => ⟨-(s:ℤ),s⟩) out hc (fun _ => t) hb
  have he : ((lo:ℝ)+hi)/2+t*(((hi:ℝ)-lo)/2)=x := by
    dsimp [t]
    field_simp [hdn]
    ring
  simpa only [RatExpr.polynomial_eval,RatExpr.eval,RationalPolynomial.eval_compose,
    RationalPolynomial.eval,Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat,
    mul_zero,add_zero,he] using h

theorem reference_cap_difference {L S x y : ℝ} (hx : x≠1) (hy : y≠1) :
    cap L S y-cap L S x=L*(y-x)*(1/2-S/((1-y)*(1-x))) := by
  unfold cap
  have hx' : 1-x≠0 := sub_ne_zero.mpr hx.symm
  have hy' : 1-y≠0 := sub_ne_zero.mpr hy.symm
  field_simp
  ring

theorem cap_monotone_prefix {L S b : ℝ} (hL : 0≤L) (hS : 0≤S)
    (hb : b<1) (hsafe : 2*S≤(1-b)^2) : MonotoneOn (cap L S) (Iic b) := by
  intro x hx y hy hxy
  have hx1 : x<1 := hx.trans_lt hb
  have hy1 : y<1 := hy.trans_lt hb
  have hden : 0<(1-y)*(1-x) := mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hx1)
  have hprod : (1-b)^2≤(1-y)*(1-x) := by
    rw [pow_two]
    exact mul_le_mul (sub_le_sub_left hy 1) (sub_le_sub_left hx 1)
      (sub_nonneg.mpr hb.le) (sub_nonneg.mpr hy1.le)
  have hfac : 0≤1/2-S/((1-y)*(1-x)) := by
    have hq : S/((1-y)*(1-x))≤1/2 := (div_le_iff₀ hden).mpr (by linarith [hsafe.trans hprod])
    linarith
  have hpos := mul_nonneg (mul_nonneg hL (sub_nonneg.mpr hxy)) hfac
  rw [←reference_cap_difference hx1.ne hy1.ne] at hpos
  exact sub_nonneg.mp hpos

theorem capSlope_antitone_prefix {L S b : ℝ} (hL : 0≤L) (hS : 0≤S)
    (hb : b<1) : AntitoneOn (capSlope L S) (Iic b) := by
  intro x hx y hy hxy
  have hdy : 0<1-y := sub_pos.mpr (hy.trans_lt hb)
  have hsq : (1-y)^2≤(1-x)^2 := pow_le_pow_left₀ hdy.le (sub_le_sub_left hxy 1) 2
  have hfrac := div_le_div_of_nonneg_left (mul_nonneg hL hS) (pow_pos hdy 2) hsq
  unfold capSlope
  linarith

theorem capGauge_antitone_prefix {L b : ℝ} (hL : 0≤L) (hb : b<1) :
    AntitoneOn (fun r => -L/(1-r)) (Iic b) := by
  intro x hx y hy hxy
  have hfrac := div_le_div_of_nonneg_left hL (sub_pos.mpr (hy.trans_lt hb)) (sub_le_sub_left hxy 1)
  simp only [neg_div]
  linarith

theorem capGaugeDerivative_antitone_prefix {L b : ℝ} (hL : 0≤L) (hb : b<1) :
    AntitoneOn (fun r => -L/(1-r)^2) (Iic b) := by
  intro x hx y hy hxy
  have hdy : 0<1-y := sub_pos.mpr (hy.trans_lt hb)
  have hfrac := div_le_div_of_nonneg_left hL (pow_pos hdy 2)
    (pow_le_pow_left₀ hdy.le (sub_le_sub_left hxy 1) 2)
  simp only [neg_div]
  linarith

end OptimalG.Certificates
