import OptimalG.VariationalSupportExtension

/-! C.23's support crossing is bracketed using an attained supporting
maximum and a fixed cap comparison; no auxiliary cap/line root is needed. -/
namespace OptimalG
open Set

noncomputable def supportingCrossing (lam m eta : ℝ) : ℝ := (eta*lam-m)/(eta-1)

theorem cap_score_at_crossing_cut_le {lam S : ℝ}
    (hlam : (22493/40000:ℝ)≤lam) (hS : (227179/10000000:ℝ)≤S) :
    Variational.capScore lam S (1529/5000)≤lam-1529/5000 := by
  have hlam0 : 0≤lam := by linarith only [hlam]
  have hprod := mul_le_mul hlam hS (by norm_num : (0:ℝ)≤227179/10000000) hlam0
  norm_num [Variational.capScore]
  nlinarith only [hlam,hprod]

theorem supportingCrossing_identity {lam m eta : ℝ} (heta : eta≠1) :
    m=eta*lam-(eta-1)*supportingCrossing lam m eta := by
  unfold supportingCrossing
  have hd : eta-1≠0 := sub_ne_zero.mpr heta
  rw [mul_div_cancel₀ _ hd]
  ring

theorem cap_support_strictMono_third {lam S eta a b : ℝ}
    (hlam : lam∈Icc (0:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Icc (1:ℝ) 2) (hcut : b≤1/3) :
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
  have hden : (2/3:ℝ)^3≤(1-r)^3 := pow_le_pow_left₀ (by norm_num)
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

theorem supportingCrossing_bounds {phi : ℝ→ℝ} {lam S eta m x t p0 : ℝ}
    (h : VerifierCurve phi lam)
    (hlam : lam∈Icc (0:ℝ) (57/100)) (hS : S∈Icc (0:ℝ) (3/100))
    (heta : eta∈Ioc (1:ℝ) 2)
    (hx : x∈Icc (57/200:ℝ) lam) (ht : t∈Icc (57/200:ℝ) (1/3))
    (hmax : x+eta*phi x=m)
    (hcap : ∀ r∈Icc (57/200:ℝ) t,phi r≤Variational.capScore lam S r)
    (hcapEnd : Variational.capScore lam S t≤lam-t)
    (hp0 : p0+eta*(lam-p0)≤m) : supportingCrossing lam m eta∈Icc t p0 := by
  have heta0 : 0≤eta := by linarith only [heta.1]
  have hupper : m≤eta*lam-(eta-1)*t := by
    by_cases hxt : x≤t
    · have hm := (cap_support_strictMono_third hlam hS ⟨heta.1.le,heta.2⟩ ht.2
        (a:=57/200)).monotoneOn ⟨hx.1,hxt⟩ ⟨ht.1,le_rfl⟩ hxt
      have h1 := mul_le_mul_of_nonneg_left (hcap x ⟨hx.1,hxt⟩) heta0
      have h2 := mul_le_mul_of_nonneg_left hcapEnd heta0
      nlinarith only [hmax,hm,h1,h2]
    · have hm := mul_le_mul_of_nonneg_left
        (h.ceiling x ⟨by linarith only [hx.1],hx.2.trans h.lam_lt_one.le⟩) heta0
      have ht' := mul_nonneg (sub_pos.mpr heta.1).le
        (show 0≤x-t by linarith only [lt_of_not_ge hxt])
      nlinarith only [hmax,hm,ht']
  unfold supportingCrossing
  constructor
  · apply (le_div_iff₀ (sub_pos.mpr heta.1)).mpr
    linarith only [hupper]
  · apply (div_le_iff₀ (sub_pos.mpr heta.1)).mpr
    nlinarith only [hp0]

end OptimalG
