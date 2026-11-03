import OptimalG.BinarySmallCentral
import OptimalG.BinaryLocalization

/-! The C.3 maximizer pattern follows from the actual affine/rational/active
score pieces and their finite slope comparisons. -/
namespace OptimalG
open Set

private theorem antitone_join {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a≤b) (hbc : b≤c) (hl : AntitoneOn f (Icc a b)) (hr : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y≤b
  · exact hl ⟨hx.1,hxy.trans hyb⟩ ⟨hy.1,hyb⟩ hxy
  · by_cases hxb : x≤b
    · exact (hr ⟨le_rfl,hbc⟩ ⟨le_of_not_ge hyb,hy.2⟩ (le_of_not_ge hyb)).trans
        (hl ⟨hx.1,hxb⟩ ⟨hab,le_rfl⟩ hxb)
    · exact hr ⟨le_of_not_ge hxb,hx.2⟩ ⟨(le_of_not_ge hxb).trans hxy,hy.2⟩ hxy

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- Head slope, cap slope and post-contact slope inequalities produce the
unimodal stationary numerator. This proves the maximizer coverage used for
both the affine-head and rational branches. -/
theorem binaryRatio_max_of_piecewise_score_slopes {p xh c t slope theta r : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (hlp : lam≤p)
    (hxh : xh ∈ Ico (0:ℝ) lam) (hxc : xh≤c) (hct : c≤t) (htl : t≤lam)
    (hshiftHead : c≤xh+1-p) (hshiftActive : t≤c+1-p)
    (hhead : ∀ q ∈ Icc (0:ℝ) xh,phi q=phi 0+slope*q)
    (hpre : ∀ a ∈ Icc (0:ℝ) c,∀ b ∈ Icc (0:ℝ) c,a≤b → slope*(b-a)≤phi b-phi a)
    (hpost : ∀ a ∈ Icc c 1,∀ b ∈ Icc c 1,a≤b → phi b-phi a≤(-theta)*(b-a))
    (hslope : -theta≤slope)
    (hcapFall : ∀ a ∈ Icc xh c,∀ b ∈ Icc xh c,a≤b → (-theta)*(b-a)≤phi b-phi a)
    (hlow : ∀ a b,0≤a → a≤b → b≤lam → a-b≤phi b-phi a)
    (hline : ∀ q ∈ Icc t lam,phi q=lam-q)
    (hr : r ∈ Ico (0:ℝ) lam) (hrshift : t≤r+1-p)
    (hroot : binaryStationaryNumerator phi lam p r=0) :
    ∀ q ∈ Ico (0:ℝ) lam,binaryRatio phi lam p q≤
      max (binaryRatio phi lam p 0) (binaryRatio phi lam p r) := by
  let k : ℝ := max (c+p-1) 0
  have hk0 : 0≤k := le_max_right _ _
  have hkk : c+p-1≤k := le_max_left _ _
  have hkx : k≤xh := by dsimp [k]; exact max_le (by linarith only [hshiftHead]) hxh.1
  have hkl : k<lam := hkx.trans_lt hxh.2
  have hcl : c≤lam := hct.trans htl
  have hxp : xh≤p := hxc.trans (hcl.trans hlp)
  have hcp : c≤p := hcl.trans hlp
  have hheadDiff {a b : ℝ} (ha : a ∈ Icc (0:ℝ) xh) (hb : b ∈ Icc (0:ℝ) xh) :
      phi b-phi a=slope*(b-a) := by rw [hhead a ha,hhead b hb]; ring
  have hinc : MonotoneOn (binaryScoreIncrement phi p) (Icc 0 k) := by
    by_cases hkh : c+p-1≤0
    · have he : k=0 := max_eq_right hkh
      intro a ha b hb hab
      have ha0 : a=0 := by rw [he] at ha; exact le_antisymm ha.2 ha.1
      have hb0 : b=0 := by rw [he] at hb; exact le_antisymm hb.2 hb.1
      simp only [ha0,hb0,le_refl]
    · have he : k=c+p-1 := max_eq_left (le_of_not_ge hkh)
      apply h.binaryScoreIncrement_monotone_of_slopes
      · intro a ha b hb hab
        exact (hheadDiff ⟨ha.1,ha.2.trans hkx⟩ ⟨hb.1,hb.2.trans hkx⟩).le
      · intro a ha b hb hab
        have hh := hpre (a+1-p) ⟨by linarith only [ha.1,hp.2],by rw [he] at ha; linarith only [ha.2]⟩
          (b+1-p) ⟨by linarith only [hb.1,hp.2],by rw [he] at hb; linarith only [hb.2]⟩ (by linarith only [hab])
        convert hh using 1 <;> ring
  have hdecHead : AntitoneOn (binaryScoreIncrement phi p) (Icc k xh) := by
    apply h.binaryScoreIncrement_antitone_of_slopes (slope:=slope)
    · intro a ha b hb hab
      exact (hheadDiff ⟨hk0.trans ha.1,ha.2⟩ ⟨hk0.trans hb.1,hb.2⟩).ge
    · intro a ha b hb hab
      have hh := hpost (a+1-p) ⟨by linarith only [hkk,ha.1],by linarith only [ha.2,hxp]⟩
        (b+1-p) ⟨by linarith only [hkk,hb.1],by linarith only [hb.2,hxp]⟩ (by linarith only [hab])
      have hm := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hab)
      nlinarith only [hh,hm]
  have hdecCap : AntitoneOn (binaryScoreIncrement phi p) (Icc xh c) := by
    apply h.binaryScoreIncrement_antitone_of_slopes (slope:= -theta) hcapFall
    intro a ha b hb hab
    have hh := hpost (a+1-p) ⟨by linarith only [hshiftHead,ha.1],by linarith only [ha.2,hcp]⟩
      (b+1-p) ⟨by linarith only [hshiftHead,hb.1],by linarith only [hb.2,hcp]⟩ (by linarith only [hab])
    convert hh using 1 <;> ring
  have hdecActive : AntitoneOn (binaryScoreIncrement phi p) (Icc c lam) := by
    apply h.binaryScoreIncrement_antitone_of_slopes (slope:= -1)
    · intro a ha b hb hab
      have hh := hlow a b (hxh.1.trans (hxc.trans ha.1)) hab hb.2
      nlinarith only [hh]
    · intro a ha b hb hab
      have hh := h.high_fall_from_line (a:=a+1-p) (b:=b+1-p) htl hline
        (by linarith only [hshiftActive,ha.1]) (by linarith only [hab]) (by linarith only [hb.2,hlp])
      nlinarith only [hh]
  have hdec := antitone_join (hkx.trans hxc) hcl (antitone_join hkx hxc hdecHead hdecCap) hdecActive
  have hNinc := h.binaryStationaryNumerator_monotone hp le_rfl (hkx.trans hxp) hkl.le hinc
  have hNdec := h.binaryStationaryNumerator_antitone hp hk0 hlp le_rfl hdec
  have hkr : k≤r := by dsimp [k]; exact max_le (by linarith only [hct,hrshift]) hr.1
  have hNk : 0≤binaryStationaryNumerator phi lam p k := by
    have hh := hNdec ⟨le_rfl,hkl.le⟩ ⟨hkr,hr.2.le⟩ hkr
    simpa only [hroot] using hh
  have hmax := h.binaryRatio_le_stationary_root hp hk0 hlp ⟨hkr,hr.2⟩ hNdec hroot
  intro q hq
  by_cases hqk : q≤k
  · have hh := h.binaryRatio_max_endpoints_of_numerator_monotone hp le_rfl
      (hkx.trans hxp) hkl hNinc q ⟨hq.1,hqk⟩
    exact hh.trans (max_le_max le_rfl (hmax k ⟨le_rfl,hkl⟩))
  · exact (hmax q ⟨le_of_not_ge hqk,hq.2⟩).trans (le_max_right _ _)

/-- The ratio maximum, combined with its two genuine scalar endpoint values,
proves every normalized low-rank binary inequality. -/
theorem binary_of_piecewise_score_slopes {p xh c t slope theta r : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (hlp : lam≤p)
    (hxh : xh ∈ Ico (0:ℝ) lam) (hxc : xh≤c) (hct : c≤t) (htl : t≤lam)
    (hshiftHead : c≤xh+1-p) (hshiftActive : t≤c+1-p)
    (hhead : ∀ q ∈ Icc (0:ℝ) xh,phi q=phi 0+slope*q)
    (hpre : ∀ a ∈ Icc (0:ℝ) c,∀ b ∈ Icc (0:ℝ) c,a≤b → slope*(b-a)≤phi b-phi a)
    (hpost : ∀ a ∈ Icc c 1,∀ b ∈ Icc c 1,a≤b → phi b-phi a≤(-theta)*(b-a))
    (hslope : -theta≤slope)
    (hcapFall : ∀ a ∈ Icc xh c,∀ b ∈ Icc xh c,a≤b → (-theta)*(b-a)≤phi b-phi a)
    (hlow : ∀ a b,0≤a → a≤b → b≤lam → a-b≤phi b-phi a)
    (hline : ∀ q ∈ Icc t lam,phi q=lam-q)
    (hr : r ∈ Ico (0:ℝ) lam) (hrshift : t≤r+1-p)
    (hroot : binaryStationaryNumerator phi lam p r=0)
    (hzero : p*curvePrimitive phi (1-p)≤lam*curvePrimitive phi p)
    (hbarrier : p*binaryRatio phi lam p r≤curvePrimitive phi p) :
    ∀ q ∈ Icc (0:ℝ) lam,normalizedBinaryTest phi p q≤lam := by
  have hmax := h.binaryRatio_max_of_piecewise_score_slopes hp hlp hxh hxc hct htl
    hshiftHead hshiftActive hhead hpre hpost hslope hcapFall hlow hline hr hrshift hroot
  have hrootBound : binaryRatio phi lam p r≤curvePrimitive phi p/p :=
    (le_div_iff₀ hp.1).mpr (by nlinarith only [hbarrier])
  have hzeroBound : binaryRatio phi lam p 0≤curvePrimitive phi p/p := by
    have hJ0 : curvePrimitive phi 0=0 := by simp [curvePrimitive]
    unfold binaryRatio
    simp only [zero_add,hJ0,sub_zero]
    exact (div_le_div_iff₀ h.lam_pos hp.1).mpr (by nlinarith only [hzero])
  apply h.binary_above_lam_of_stationary hp hlp hzero
  intro q hq _
  exact (hmax q ⟨hq.1.le,hq.2⟩).trans (max_le hzeroBound hrootBound)

end VerifierCurve
end OptimalG
