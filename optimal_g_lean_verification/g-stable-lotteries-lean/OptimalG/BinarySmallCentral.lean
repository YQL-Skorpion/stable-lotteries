import OptimalG.BinaryHighRanks
import OptimalG.BinaryCapReduction
import OptimalG.SigmaPrimitive
import OptimalG.BinaryAreaBounds
import OptimalG.TailContact

/-! Actual two-class inequalities through mass 0.775. The remaining checks
are polynomial or rational scalar expressions on explicitly bounded boxes. -/
namespace OptimalG
open Set MeasureTheory

noncomputable def binaryCentralUpperArea (lam S c r : ℝ) : ℝ :=
  min (binaryAreaUpper (309/1000) (348541/1000000) (87/1000000000) (24/100000) r)
    (Variational.capDeficit lam S c-Variational.capSlack lam S c*(r-c)+(309/2000)*(r-c)^2)

noncomputable def binaryHeadCapError (lam S phi0 slope xh c r : ℝ) : ℝ :=
  if r ≤ xh then phi0*r+slope*r^2/2-Variational.cap lam S r
  else if 9/25≤r then Variational.quadratic lam r-S-Variational.cap lam S r
  else if c≤r then min 0 (Variational.quadratic lam r-S+binaryCentralUpperArea lam S c r-Variational.cap lam S r)
  else 0

/-- These are scalar residuals of the completed affine head and the straight
middle primitive, not assumed binary inequalities of the unknown curve. -/
structure BinarySmallIntervals (lam S phi0 slope xh c : ℝ) : Prop where
  head_zero : ∀ p ∈ Icc (0:ℝ) xh,
    Variational.quadratic lam (1-p)-S ≤ lam*(phi0+slope*p/2)
  middle_zero : ∀ p ∈ Icc xh (16/25:ℝ),
    p*(Variational.quadratic lam (1-p)-S) ≤ lam*(Variational.quadratic lam p-S)
  derivative_margin : ∀ p ∈ Icc (1-lam) (13/20:ℝ),
    0 ≤ p*(1+phi0-2*lam)-p^2/2+S
  central_anchor : ∀ p ∈ Icc (13/20:ℝ) (31/40:ℝ),
    Variational.quadratic lam p-S+
      p*(lam-9/50-1+p-phi0-slope*(9/50)) ≤ 0
  central_residual : ∀ p ∈ Icc (13/20:ℝ) (31/40:ℝ), ∀ q ∈ Icc (0:ℝ) (9/50:ℝ),
    q*(Variational.quadratic lam p-S+p*(lam/2-phi0-slope*q/2)-lam*S/(p-q))+
      p*binaryHeadCapError lam S phi0 slope xh c (q+1-p) ≤ 0

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem affine_head_primitive {xh slope q : ℝ}
    (haff : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hq : q ∈ Icc (0:ℝ) xh) :
    curvePrimitive phi q=phi 0*q+slope*q^2/2 := by
  have he : curvePrimitive phi q=∫ r in (0:ℝ)..q,phi 0+slope*r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hq.1] at hr
    exact haff r ⟨hr.1,hr.2.trans hq.2⟩
  rw [he]
  have hd (r : ℝ) : HasDerivAt (fun r => phi 0*r+slope*r^2/2) (phi 0+slope*r) r := by
    convert! ((hasDerivAt_id r).const_mul (phi 0)).add
      (((hasDerivAt_id r).pow 2).const_mul slope |>.div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    ((by fun_prop : Continuous (fun r : ℝ => phi 0+slope*r)).intervalIntegrable 0 q)]
  simp

/-- The primitive relative to Q is antitone because its actual derivative is
at most the score ceiling. -/
theorem primitive_relative_quadratic_antitone :
    AntitoneOn (fun r => curvePrimitive phi r-Variational.quadratic lam r) (Icc 0 1) := by
  intro a ha b hb hab
  have hi : IntervalIntegrable (scoreDefect phi lam) volume a b :=
    (h.scoreDefect_continuous.mono (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hab
  have hh := intervalIntegral.integral_nonneg (μ:=volume) hab (fun r hr =>
    h.scoreDefect_nonneg ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩)
  rw [h.scoreDefect_integral ha.1 hab hb.2] at hh
  linarith

/-- The high fall bound starts wherever the straight middle score starts. -/
theorem high_fall_from_line {t a b : ℝ} (ht : t ≤ lam)
    (hline : ∀ r ∈ Icc t lam,phi r=lam-r)
    (ha : t ≤ a) (hab : a ≤ b) (hb : b ≤ 1) : phi b-phi a ≤ a-b := by
  by_cases hal : lam ≤ a
  · exact h.high_fall a b hal hab hb
  · by_cases hbl : b ≤ lam
    · rw [hline a ⟨ha,(le_of_not_ge hal)⟩,hline b ⟨ha.trans hab,hbl⟩]
      ring_nf
      rfl
    · have hh := h.high_fall lam b le_rfl (le_of_not_ge hbl) hb
      rw [h.at_lam,hline a ⟨ha,(le_of_not_ge hal)⟩] at *
      linarith

/-- The correctly oriented q=0 test is proved from the actual head and the
middle primitive. Above the middle segment only the integrated score ceiling
is used, rather than falsely asserting the high primitive remains quadratic. -/
theorem binary_zero_through_small {S xh slope c p : ℝ}
    (hlam : lam ∈ Icc (1/2:ℝ) (3/5:ℝ)) (hxh : xh ∈ Icc (9/50:ℝ) (7/20:ℝ))
    (haff : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hflat : ∀ r ∈ Icc (9/25:ℝ) (31/40:ℝ),curvePrimitive phi r=Variational.quadratic lam r-S)
    (hcap : ∀ r ∈ Icc xh (53/100:ℝ),curvePrimitive phi r≤Variational.cap lam S r)
    (hn : BinarySmallIntervals lam S (phi 0) slope xh c)
    (hp : p ∈ Ioc (0:ℝ) (13/20:ℝ)) :
    p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p := by
  have hleft := hflat (9/25) ⟨le_rfl,by norm_num⟩
  have hright := hflat (31/40) ⟨by norm_num,le_rfl⟩
  have hupper (r : ℝ) (hr : r ∈ Icc (9/25:ℝ) 1) :
      curvePrimitive phi r≤Variational.quadratic lam r-S := by
    have hh := h.primitive_relative_quadratic_antitone
      ⟨by norm_num,by norm_num⟩ ⟨by linarith [hr.1],hr.2⟩ hr.1
    dsimp only at hh
    rw [hleft] at hh
    linarith
  have hlower (r : ℝ) (hr : r ∈ Icc (0:ℝ) (31/40:ℝ)) :
      Variational.quadratic lam r-S≤curvePrimitive phi r := by
    have hh := h.primitive_relative_quadratic_antitone
      ⟨hr.1,by linarith [hr.2]⟩ ⟨by norm_num,by norm_num⟩ hr.2
    dsimp only at hh
    rw [hright] at hh
    linarith
  by_cases hph : p ≤ xh
  · have hu := hupper (1-p) ⟨by linarith [hxh.2],by linarith [hp.1]⟩
    have hm := mul_le_mul_of_nonneg_left (hu.trans (hn.head_zero p ⟨hp.1.le,hph⟩)) hp.1.le
    rw [h.affine_head_primitive haff ⟨hp.1.le,hph⟩]
    nlinarith only [hm]
  · by_cases hp64 : p ≤ 16/25
    · have hu := mul_le_mul_of_nonneg_left
        (hupper (1-p) ⟨by linarith,by linarith [hp.1]⟩) hp.1.le
      have hl := mul_le_mul_of_nonneg_left (hlower p ⟨hp.1.le,by linarith⟩) h.lam_pos.le
      linarith [hn.middle_zero p ⟨le_of_not_ge hph,hp64⟩]
    · exact h.binary_zero_split_of_cap hp.1 (hflat p ⟨by linarith,by linarith [hp.2]⟩)
        (hcap (1-p) ⟨by linarith [hp.2,hxh.2],by linarith⟩)

/-- All low splits through mass 0.65 reduce to explicit scalar checks. -/
theorem binary_small_low {S xh slope c p : ℝ}
    (hlam : lam ∈ Icc (1/2:ℝ) (3/5:ℝ)) (hxh : xh ∈ Icc (9/50:ℝ) (7/20:ℝ))
    (haff : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hflat : ∀ r ∈ Icc (9/25:ℝ) (31/40:ℝ),curvePrimitive phi r=Variational.quadratic lam r-S)
    (hcap : ∀ r ∈ Icc xh (53/100:ℝ),curvePrimitive phi r≤Variational.cap lam S r)
    (hlow : ∀ r ∈ Icc (0:ℝ) lam,phi 0-r≤phi r)
    (hn : BinarySmallIntervals lam S (phi 0) slope xh c)
    (hp : p ∈ Ioc (0:ℝ) (13/20:ℝ)) :
    ∀ q,0≤q → q≤p → q≤lam → normalizedBinaryTest phi p q≤lam := by
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1,by linarith [hp.2]⟩
  have hgap : 1≤(p/curvePrimitive phi p)*(phi 0-lam+1-p) := by
    by_cases hps : p≤1-lam
    · exact h.normalized_binary_gap_small hp0 hps
    · exact h.normalized_binary_gap_flat hp0
        (hflat p ⟨by linarith [hlam.2],by linarith [hp.2]⟩)
        (hn.derivative_margin p ⟨le_of_not_ge hps,hp.2⟩)
  exact h.normalized_binary_of_zero_split hp0 hlow hgap
    (h.binary_zero_through_small hlam hxh haff hflat hcap hn hp)

/-- The central error profile is bounded against the actual primitive by
integrating score slopes from both the contact and the reference rank. -/
theorem binary_central_upper_area {S c : ℝ}
    (hc : 0≤c) (hcp : c≤348541/1000000)
    (hJc : curvePrimitive phi c=Variational.cap lam S c)
    (hscorec : phi c=Variational.capScore lam S c)
    (harea : binarySlackArea phi lam S (348541/1000000)≤87/1000000000)
    (hscore : scoreDefect phi lam (348541/1000000)≤24/100000)
    (hfall : ∀ a ∈ Icc c (9/25:ℝ),∀ b ∈ Icc c (9/25:ℝ),a≤b →
      scoreDefect phi lam a-scoreDefect phi lam b≤(309/1000)*(b-a)) :
    ∀ r ∈ Icc c (9/25:ℝ),curvePrimitive phi r≤
      Variational.quadratic lam r-S+binaryCentralUpperArea lam S c r := by
  intro r hr
  have href := h.binarySlackArea_upper hc (by norm_num : (9/25:ℝ)≤1)
    ⟨hcp,by norm_num⟩ harea hscore
    (fun u hu => hfall u ⟨hu.1,by linarith only [hu.2]⟩
      (348541/1000000) ⟨hcp,by norm_num⟩ hu.2) r hr
  have hini := h.binarySlackArea_forward_upper (S:=S) hc hr.1
    (by linarith only [hr.2]) (fun u hu => hfall c ⟨le_rfl,hr.1.trans hr.2⟩
      u ⟨hu.1,hu.2.trans hr.2⟩ hu.1)
  have hEc : binarySlackArea phi lam S c=Variational.capDeficit lam S c := by
    unfold binarySlackArea Variational.capDeficit
    rw [hJc]
    ring
  have hsc : scoreDefect phi lam c=Variational.capSlack lam S c := by
    unfold scoreDefect Variational.capSlack
    rw [hscorec]
  rw [hEc,hsc] at hini
  have hb : binarySlackArea phi lam S r≤binaryCentralUpperArea lam S c r := by
    apply le_min href
    linarith only [hini]
  unfold binarySlackArea at hb
  linarith only [hb]

/-- The central strip q≤0.18 uses its exact rational residual; monotonicity
from the derivative anchor covers every larger low split. -/
theorem binary_central_low {S xh slope c p : ℝ}
    (hlam : lam ∈ Icc (1/2:ℝ) (3/5:ℝ)) (hxh : xh ∈ Icc (9/50:ℝ) (7/20:ℝ))
    (haff : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hflat : ∀ r ∈ Icc (9/25:ℝ) (31/40:ℝ),curvePrimitive phi r=Variational.quadratic lam r-S)
    (hcap : ∀ r ∈ Icc xh (53/100:ℝ),curvePrimitive phi r≤Variational.cap lam S r)
    (hline : ∀ r ∈ Icc (9/25:ℝ) (31/40:ℝ),phi r=lam-r)
    (hfall : ∀ a b,0≤a → a≤b → b≤lam → a-b≤phi b-phi a)
    (hmid : ∀ r ∈ Icc c (9/25:ℝ),curvePrimitive phi r≤
      Variational.quadratic lam r-S+binaryCentralUpperArea lam S c r)
    (hn : BinarySmallIntervals lam S (phi 0) slope xh c)
    (hp : p ∈ Icc (13/20:ℝ) (31/40:ℝ)) :
    ∀ q ∈ Icc (0:ℝ) lam, normalizedBinaryTest phi p q≤lam := by
  have hp0 : p ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hp.1],by linarith [hp.2]⟩
  have hpl : lam≤p := by linarith [hlam.2,hp.1]
  have hflatp := hflat p ⟨by linarith [hp.1],hp.2⟩
  apply h.binary_of_initial_strip (a:=9/50) (b:=lam) hp0 (by norm_num) (by linarith [hlam.1]) hpl
  · intro q hq
    exact hfall (9/50) q (by norm_num) hq.1 hq.2
  · intro q hq
    have hh := h.high_fall_from_line (a:=9/50+1-p) (b:=q+1-p)
      (by linarith [hlam.1]) (fun r hr => hline r ⟨hr.1,by linarith [hr.2,hlam.2]⟩)
      (by linarith [hp.2]) (by linarith [hq.1]) (by linarith [hq.2])
    linarith only [hh]
  · rw [hflatp,haff (9/50) ⟨by norm_num,hxh.1⟩,
      hline (9/50+1-p) ⟨by linarith [hp.2],by linarith [hp.1]⟩]
    convert hn.central_anchor p hp using 1 <;> ring
  · intro q hq
    apply h.binary_central_of_checked_expression hp0 (by linarith [hq.2,hp.1]) hflatp
      (h.affine_head_primitive haff ⟨hq.1,hq.2.trans hxh.1⟩) _ (hn.central_residual p hp q hq)
    by_cases hr : q+1-p≤xh
    · rw [binaryHeadCapError,if_pos hr,h.affine_head_primitive haff ⟨by linarith [hp.2,hq.1],hr⟩]
      linarith
    · by_cases hrline : 9/25≤q+1-p
      · rw [binaryHeadCapError,if_neg hr,if_pos hrline,
          hflat (q+1-p) ⟨hrline,by linarith only [hq.2,hp.1]⟩]
        linarith
      · by_cases hrc : c≤q+1-p
        · rw [binaryHeadCapError,if_neg hr,if_neg hrline,if_pos hrc,add_min,add_zero]
          apply le_min (hcap (q+1-p) ⟨le_of_not_ge hr,by linarith only [hq.2,hp.1]⟩)
          have hh := hmid (q+1-p) ⟨hrc,le_of_not_ge hrline⟩
          linarith only [hh]
        · rw [binaryHeadCapError,if_neg hr,if_neg hrline,if_neg hrc,add_zero]
          exact hcap (q+1-p) ⟨le_of_not_ge hr,by linarith only [hp.1,hq.2]⟩

end VerifierCurve
end OptimalG
