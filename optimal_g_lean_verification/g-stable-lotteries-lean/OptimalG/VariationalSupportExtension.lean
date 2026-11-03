import OptimalG.SmallMassCapSupport

/-! Local variational support maxima extend to all low ranks. The head and
cap give the left extension; the score ceiling gives the right extension. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem support_before_test_interval {S eta slope : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) (1000/691)) (hslope : -(691/1000:ℝ)≤slope)
    (hhead : ∀ x∈Icc (0:ℝ) (527/2000),phi x=phi 0+slope*x)
    (hcap : ∀ x∈Icc (527/2000:ℝ) (57/200),phi x=Variational.capScore lam S x) :
    ∀ x∈Icc (0:ℝ) (57/200),x+eta*phi x≤(57/200:ℝ)+eta*phi (57/200) := by
  have heta0 : 0≤eta := by linarith only [heta.1]
  have hmult := mul_le_mul_of_nonneg_left hslope heta0
  have hs : 0≤1+eta*slope := by nlinarith only [hmult,heta.2]
  have hj := hhead (527/2000) ⟨by norm_num,le_rfl⟩
  have hh0 : eta*phi 0≤(527/2000:ℝ)+eta*phi (527/2000) := by
    rw [hj]
    nlinarith only [hs]
  have hheadSupport := affine_score_support hhead hh0 (le_refl ((527/2000:ℝ)+eta*phi (527/2000)))
  have hmono := (cap_support_strictMono_up_to
    ⟨by linarith only [hlam.1],hlam.2⟩ hS
    ⟨heta.1,by linarith only [heta.2]⟩ (by norm_num : (57/200:ℝ)≤3/10)
    (a:=527/2000)).monotoneOn
  have hcapSupport (x : ℝ) (hx : x∈Icc (527/2000:ℝ) (57/200)) :
      x+eta*phi x≤(57/200:ℝ)+eta*phi (57/200) := by
    have hh := hmono hx ⟨by norm_num,le_rfl⟩ hx.2
    dsimp only at hh
    rwa [←hcap x hx,←hcap (57/200) ⟨by norm_num,le_rfl⟩] at hh
  intro x hx
  by_cases hxh : x≤527/2000
  · exact (hheadSupport x ⟨hx.1,hxh⟩).trans
      (hcapSupport (527/2000) ⟨le_rfl,by norm_num⟩)
  · exact hcapSupport x ⟨(lt_of_not_ge hxh).le,hx.2⟩

theorem local_support_to_global {S p eta target slope : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) (1000/691)) (hslope : -(691/1000:ℝ)≤slope)
    (hp : p∈Icc (0:ℝ) (19/50))
    (hhead : ∀ x∈Icc (0:ℝ) (527/2000),phi x=phi 0+slope*x)
    (hcap : ∀ x∈Icc (527/2000:ℝ) (57/200),phi x=Variational.capScore lam S x)
    (hline : phi (19/50)=lam-19/50)
    (hsupport : ∀ x∈Icc (max (57/200) p) (19/50),x+eta*phi x≤target) :
    ∀ x∈Icc p lam,x+eta*phi x≤target := by
  have hleft := h.support_before_test_interval hlam hS heta hslope hhead hcap
  have heta0 : 0≤eta := by linarith only [heta.1]
  intro x hx
  by_cases hxl : x≤57/200
  · have hloc := hsupport (57/200) ⟨max_le le_rfl (hx.1.trans hxl),by norm_num⟩
    exact (hleft x ⟨hp.1.trans hx.1,hxl⟩).trans hloc
  · by_cases hxr : x≤19/50
    · exact hsupport x ⟨max_le (lt_of_not_ge hxl).le hx.1,hxr⟩
    · have hloc := hsupport (19/50) ⟨max_le (by norm_num) hp.2,le_rfl⟩
      have hcapx := mul_le_mul_of_nonneg_left
        (h.ceiling x ⟨hp.1.trans hx.1,hx.2.trans h.lam_lt_one.le⟩) heta0
      have hprod := mul_nonneg (sub_nonneg.mpr heta.1)
        (show 0≤x-19/50 by linarith only [lt_of_not_ge hxr])
      rw [hline] at hloc
      nlinarith only [hloc,hcapx,hprod]

end VerifierCurve
end OptimalG
