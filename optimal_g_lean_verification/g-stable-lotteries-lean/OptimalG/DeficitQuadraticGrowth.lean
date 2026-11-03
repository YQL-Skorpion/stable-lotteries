import OptimalG.TailSelectedDeficit

/-! Convexity of the actual score deficit gives quadratic growth control of
its primitive deficit from one endpoint value. -/
namespace OptimalG
open Set MeasureTheory

theorem convex_integral_quadratic_growth {f : ℝ→ℝ} {a b p : ℝ}
    (hab : a<b) (hp : p∈Icc a b) (hcont : ContinuousOn f (Icc a b))
    (hconv : ConvexOn ℝ (Icc a b) f) (hzero : f a=0) :
    (∫ r in a..p,f r)≤((p-a)/(b-a))^2*(∫ r in a..b,f r) := by
  let theta := (p-a)/(b-a)
  have htheta : theta∈Icc (0:ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr hp.1) (sub_pos.mpr hab).le,
      (div_le_one (sub_pos.mpr hab)).mpr (by linarith only [hp.2])⟩
  have hw : p-a=theta*(b-a) := by dsimp [theta]; field_simp [(sub_pos.mpr hab).ne']
  have hmap (c : ℝ) (hc : c∈Icc a b) :
      MapsTo (fun u : ℝ=>a+(c-a)*u) (Icc 0 1) (Icc a b) := by
    intro u hu
    have hlo := mul_nonneg (sub_nonneg.mpr hc.1) hu.1
    have hhi := mul_le_mul_of_nonneg_left hu.2 (sub_nonneg.mpr hc.1)
    constructor <;> linarith only [hlo,hhi,hc.2]
  have hc (c : ℝ) (hc : c∈Icc a b) :
      ContinuousOn (fun u : ℝ=>f (a+(c-a)*u)) (Icc 0 1) :=
    hcont.comp (by fun_prop) (hmap c hc)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
    ((hc p hp).intervalIntegrable_of_Icc (μ:=volume) (by norm_num))
    (((hc b ⟨hab.le,le_rfl⟩).const_mul theta).intervalIntegrable_of_Icc (μ:=volume) (by norm_num))
    (fun u hu => by
      have hcv := hconv.2 ⟨le_rfl,hab.le⟩ (hmap b ⟨hab.le,le_rfl⟩ hu)
        (sub_nonneg.mpr htheta.2) htheta.1 (by ring : 1-theta+theta=1)
      have he : (1-theta)*a+theta*(a+(b-a)*u)=a+(p-a)*u := by rw [hw]; ring
      simpa only [smul_eq_mul,he,hzero,mul_zero,zero_add] using hcv)
  rw [intervalIntegral.integral_const_mul] at hi
  have hid (c : ℝ) : (c-a)*(∫ u in (0:ℝ)..1,f (a+(c-a)*u))=∫ r in a..c,f r := by
    have hh := intervalIntegral.smul_integral_comp_add_mul (f:=f) (a:=0) (b:=1) (c-a) a
    have he : a+(c-a)=c := by ring
    simpa only [smul_eq_mul,mul_zero,mul_one,add_zero,he] using hh
  have hm := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hp.1)
  rw [hid p] at hm
  calc
    (∫ r in a..p,f r)≤(p-a)*(theta*(∫ u in (0:ℝ)..1,f (a+(b-a)*u))) := hm
    _=theta^2*((b-a)*(∫ u in (0:ℝ)..1,f (a+(b-a)*u))) := by rw [hw]; ring
    _=theta^2*(∫ r in a..b,f r) := by rw [hid b]

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem primitiveDefect_quadratic_growth {S a b p : ℝ}
    (hconc : ConcaveOn ℝ (Icc lam 1) phi) (ha : lam≤a) (hab : a<b) (hb : b≤1)
    (hp : p∈Icc a b) (hstart : curvePrimitive phi a=Variational.quadratic lam a-S)
    (hzero : phi a=lam-a) :
    primitiveDefect phi lam S p≤((p-a)/(b-a))^2*primitiveDefect phi lam S b := by
  have hc := (h.scoreDefect_convex hconc).subset (Icc_subset_Icc ha hb) (convex_Icc a b)
  have hcont := h.scoreDefect_continuous.mono
    (Icc_subset_Icc (h.lam_pos.le.trans ha) hb)
  have hz : scoreDefect phi lam a=0 := by simp [scoreDefect,hzero]
  have hh := convex_integral_quadratic_growth hab hp hcont hc hz
  rw [←h.primitiveDefect_eq_integral (h.lam_pos.le.trans ha) hp.1 (hp.2.trans hb) hstart,
    ←h.primitiveDefect_eq_integral (h.lam_pos.le.trans ha) hab.le hb hstart] at hh
  exact hh

theorem high_deficit_quadratic_bound {S p : ℝ}
    (hconc : ConcaveOn ℝ (Icc lam 1) phi) (hL : lam≤391/500)
    (hp : p∈Icc (391/500:ℝ) (7/8))
    (hstart : curvePrimitive phi (391/500)=Variational.quadratic lam (391/500)-S)
    (hzero : phi (391/500)=lam-391/500)
    (hend : primitiveDefect phi lam S (7/8)≤17/5000) :
    primitiveDefect phi lam S p≤(17/5000)*((p-391/500)/(93/1000))^2 := by
  have hh := h.primitiveDefect_quadratic_growth hconc hL (by norm_num) (by norm_num) hp hstart hzero
  have hm := mul_le_mul_of_nonneg_left hend (sq_nonneg ((p-391/500)/(93/1000)))
  norm_num only [show (7/8:ℝ)-391/500=93/1000 by norm_num] at hh
  nlinarith only [hh,hm]

end VerifierCurve
end OptimalG
