import OptimalG.SmallMassSupport
import OptimalG.VariationalCapSlope

/-! The supporting-line construction for the intermediate small-mass strip.
The cap portion is monotone for every coefficient in [1,2]; only the head's
zero endpoint remains a scalar certificate. -/
namespace OptimalG
open Set

theorem cap_support_strictMono_up_to {lam S eta a b : ℝ}
    (hlam : lam∈Icc (0:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) 2) (hcut : b≤3/10) :
    StrictMonoOn (fun x => x+eta*Variational.capScore lam S x) (Icc a b) := by
  have hder (r : ℝ) (hr : r≤b) :
      HasDerivAt (fun x => x+eta*Variational.capScore lam S x)
        (1-eta*(2*lam*S/(1-r)^3)) r := by
    have hh := (hasDerivAt_id r).add
      ((Variational.capScore_hasDerivAt lam S r (by linarith only [hr,hcut])).const_mul eta)
    convert! hh using 1 <;> ring
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun r hr => (hder r hr.2).continuousAt.continuousWithinAt)
  intro r hr
  have hrr := (interior_subset hr).2
  rw [(hder r hrr).deriv]
  have hden : (7/10:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num)
    (by linarith only [hrr,hcut]) 3
  have hdenpos : 0<(1-r)^3 := pow_pos (by linarith only [hrr,hcut]) 3
  have hLS := mul_le_mul hlam.2 hS.2 hS.1 (by norm_num : (0:ℝ)≤57/100)
  have heta0 : 0≤eta := by linarith only [heta.1]
  have hnum := mul_le_mul_of_nonneg_left (show 2*lam*S≤171/5000 by
    nlinarith only [hLS]) heta0
  have hfrac : eta*(2*lam*S)/(1-r)^3<1 := by
    apply (div_lt_iff₀ hdenpos).mpr
    norm_num at hden
    nlinarith only [hnum,heta.2,hden]
  rw [mul_div_assoc] at hfrac
  linarith only [hfrac]

theorem cap_support_strictMono {lam S eta a : ℝ}
    (hlam : lam∈Icc (0:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) 2) :
    StrictMonoOn (fun x => x+eta*Variational.capScore lam S x) (Icc a (7/25)) :=
  cap_support_strictMono_up_to hlam hS heta (by norm_num)

theorem cap_support_monotone {lam S eta a : ℝ}
    (hlam : lam∈Icc (0:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) 2) :
    MonotoneOn (fun x => x+eta*Variational.capScore lam S x) (Icc a (7/25)) :=
  (cap_support_strictMono hlam hS heta).monotoneOn

noncomputable def smallMassCapEta (phi : ℝ→ℝ) (lam p beta target : ℝ) : ℝ :=
  min (1+beta*p) (1+(target-lam)/phi (7/25))

namespace VerifierCurve
variable {phi : ℝ→ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem smallMass_cap_support {S p beta target slope : ℝ}
    (hlam : lam∈Icc (1/2:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (hbp : beta*p∈Icc (0:ℝ) 1) (hmt : lam≤target)
    (hhead : ∀ x∈Icc (0:ℝ) (527/2000),phi x=phi 0+slope*x)
    (hcap : ∀ x∈Icc (527/2000:ℝ) (7/25),phi x=Variational.capScore lam S x)
    (hzero : smallMassCapEta phi lam p beta target*phi 0≤target) :
    1≤smallMassCapEta phi lam p beta target ∧
    smallMassCapEta phi lam p beta target≤1+beta*p ∧
    ∀ x∈Icc (0:ℝ) lam,x+smallMassCapEta phi lam p beta target*phi x≤target := by
  let eta := smallMassCapEta phi lam p beta target
  have hpos : 0<phi (7/25) := h.positive ⟨by norm_num,by linarith only [hlam.1]⟩
  have helo : 1≤eta := le_min (by linarith only [hbp.1])
    (by have hh := div_nonneg (sub_nonneg.mpr hmt) hpos.le; linarith only [hh])
  have heleft : eta≤1+beta*p := min_le_left _ _
  have heright : eta≤1+(target-lam)/phi (7/25) := min_le_right _ _
  have hehi : eta≤2 := by linarith only [heleft,hbp.2]
  have hebound : (eta-1)*phi (7/25)≤target-lam := by
    apply (le_div_iff₀ hpos).mp
    linarith only [heright]
  have htail (x : ℝ) (hx : x∈Icc (7/25:ℝ) lam) : x+eta*phi x≤target := by
    have hscore := h.decreasing.antitoneOn
      ⟨by norm_num,by linarith only [h.lam_lt_one]⟩
      ⟨by linarith only [hx.1],hx.2.trans h.lam_lt_one.le⟩ hx.1
    have hmul := mul_le_mul_of_nonneg_left hscore (by linarith only [helo] : 0≤eta-1)
    have hceiling := h.ceiling x ⟨by linarith only [hx.1],hx.2.trans h.lam_lt_one.le⟩
    nlinarith only [hmul,hceiling,hebound]
  have hmono := cap_support_monotone ⟨by linarith only [hlam.1],hlam.2⟩ hS ⟨helo,hehi⟩
    (a:=527/2000)
  have hmiddle (x : ℝ) (hx : x∈Icc (527/2000:ℝ) (7/25)) : x+eta*phi x≤target := by
    have hh := hmono hx ⟨by norm_num,le_rfl⟩ hx.2
    dsimp only at hh
    rw [← hcap x hx,← hcap (7/25) ⟨by norm_num,le_rfl⟩] at hh
    exact hh.trans (htail (7/25) ⟨le_rfl,by linarith only [hlam.1]⟩)
  have hfirst := affine_score_support hhead hzero (hmiddle (527/2000) ⟨le_rfl,by norm_num⟩)
  refine ⟨helo,heleft,?_⟩
  intro x hx
  by_cases hxh : x≤527/2000
  · exact hfirst x ⟨hx.1,hxh⟩
  · by_cases hxe : x≤7/25
    · exact hmiddle x ⟨(lt_of_not_ge hxh).le,hxe⟩
    · exact htail x ⟨(lt_of_not_ge hxe).le,hx.2⟩

end VerifierCurve
end OptimalG
