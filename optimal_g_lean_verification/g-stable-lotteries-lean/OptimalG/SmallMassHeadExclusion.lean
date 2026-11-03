import OptimalG.SmallMassCapSupport
import OptimalG.SmallMassCurveTransport

/-! The numerical head exclusion in C.4 needs only one strict scalar test.
Cap monotonicity and affine interpolation then exclude every head rank. -/
namespace OptimalG
open Set

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem supportMinimum_minimizer_ge_ell {S m slope x : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hm : lam<m)
    (heta : supportMinimum phi lam m∈Icc (1:ℝ) 2)
    (hhead : ∀ u∈Icc (0:ℝ) (527/2000),phi u=phi 0+slope*u)
    (hcap : ∀ u∈Icc (527/2000:ℝ) (7/25),phi u=Variational.capScore lam S u)
    (hzero : supportMinimum phi lam m*phi 0<m)
    (hx : x∈Ico (0:ℝ) lam)
    (hmin : supportMinimum phi lam m=(m-x)/phi x) : 7/25≤x := by
  let eta := supportMinimum phi lam m
  have hcontact : x+eta*phi x=m := by
    dsimp [eta]
    rw [hmin,div_mul_cancel₀ _ (h.positive hx).ne']
    ring
  have hmono := cap_support_strictMono
    ⟨by linarith only [hlam.1],hlam.2⟩ hS heta (a:=527/2000)
  have hendpoint : (7/25:ℝ)+eta*phi (7/25)≤m :=
    h.supportMinimum_supports hm ⟨by norm_num,by linarith only [hlam.1]⟩
  have hmiddle (u : ℝ) (hu : u∈Ico (527/2000:ℝ) (7/25)) : u+eta*phi u<m := by
    have hh := hmono ⟨hu.1,hu.2.le⟩ ⟨by norm_num,le_rfl⟩ hu.2
    dsimp only at hh
    rw [←hcap u ⟨hu.1,hu.2.le⟩,←hcap (7/25) ⟨by norm_num,le_rfl⟩] at hh
    exact hh.trans_le hendpoint
  have hjoin := hmiddle (527/2000) ⟨le_rfl,by norm_num⟩
  have hmax : max (eta*phi 0) ((527/2000:ℝ)+eta*phi (527/2000))<m :=
    max_lt hzero hjoin
  have hfirst := affine_score_support hhead
    (le_max_left (eta*phi 0) ((527/2000:ℝ)+eta*phi (527/2000)))
    (le_max_right (eta*phi 0) ((527/2000:ℝ)+eta*phi (527/2000)))
  by_contra hn
  have hxe : x<7/25 := lt_of_not_ge hn
  have hh : x+eta*phi x<m := by
    by_cases hxh : x≤527/2000
    · exact (hfirst x ⟨hx.1,hxh⟩).trans_lt hmax
    · exact hmiddle x ⟨(lt_of_not_ge hxh).le,hxe⟩
  linarith only [hh,hcontact]

theorem supportMinimum_minimizer_score_le_cap {S m slope x : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hm : lam<m) (heta : supportMinimum phi lam m∈Icc (1:ℝ) 2)
    (hhead : ∀ u∈Icc (0:ℝ) (527/2000),phi u=phi 0+slope*u)
    (hcap : ∀ u∈Icc (527/2000:ℝ) (7/25),phi u=Variational.capScore lam S u)
    (hzero : supportMinimum phi lam m*phi 0<m)
    (hx : x∈Ico (0:ℝ) lam)
    (hmin : supportMinimum phi lam m=(m-x)/phi x) :
    phi x≤Variational.capScore lam S (7/25) := by
  have hxe := h.supportMinimum_minimizer_ge_ell hlam hS hm heta hhead hcap hzero hx hmin
  have hh := h.decreasing.antitoneOn ⟨by norm_num,by linarith only [h.lam_lt_one]⟩
    ⟨hx.1,hx.2.le.trans h.lam_lt_one.le⟩ hxe
  rwa [hcap (7/25) ⟨by norm_num,le_rfl⟩] at hh

end VerifierCurve
end OptimalG
