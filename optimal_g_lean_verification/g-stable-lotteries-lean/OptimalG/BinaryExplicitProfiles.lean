import OptimalG.BinaryAreaBounds
import OptimalG.BinarySmallCentral
import OptimalG.TailContact

/-! Explicit rational/cone profiles for the C.18 finite checks. Each profile
is bounded against the actual score or actual primitive of the completed curve. -/
namespace OptimalG
open Set Variational

noncomputable def binaryAreaCutoff (lam S c k : ℝ) : ℝ :=
  c+capDeficit lam S c/capSlack lam S c+capSlack lam S c/(2*k)
noncomputable def binaryAreaCone (lam S c k r : ℝ) : ℝ :=
  k/2*((max (binaryAreaCutoff lam S c k-r) 0)^2-
    (max (binaryAreaCutoff lam S c k-capSlack lam S c/k-r) 0)^2)
noncomputable def binaryScoreCone (lam S c t k r : ℝ) : ℝ :=
  capSlack lam S c*max (binaryAreaCutoff lam S c k-r) 0/(capSlack lam S c/k+t-r)
noncomputable def binaryAreaLower (lam S phi0 slope xh c t k r : ℝ) : ℝ :=
  if r≤xh then phi0*r+slope*r^2/2-quadratic lam r+S
  else if r≤c then capDeficit lam S r
  else if r≤t then binaryAreaCone lam S c k r else 0
noncomputable def binaryScoreLower (lam S phi0 slope xh c t k r : ℝ) : ℝ :=
  if r≤xh then lam-r-(phi0+slope*r)
  else if r≤c then capSlack lam S r
  else if r≤t then binaryScoreCone lam S c t k r else 0
noncomputable def binaryAreaUpperProfile
    (lam S phi0 slope xh c k pref epsArea epsScore r : ℝ) : ℝ :=
  if r≤xh then phi0*r+slope*r^2/2-quadratic lam r+S
  else if r≤c then capDeficit lam S r
  else binaryAreaUpper k pref epsArea epsScore r

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The finite lower-area expression C.17 is below the actual primitive
slack on every rank, including the affine head and the zero-slack interval. -/
theorem binaryAreaLower_le {S slope xh c t z0 k : ℝ}
    (hxh : 0≤xh) (hxc : xh≤c) (hct : c≤t) (htz : t≤z0) (hz1 : z0≤1)
    (hk : 0<k) (hs : 0<capSlack lam S c)
    (hhead : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hcapJ : ∀ r ∈ Icc xh c,curvePrimitive phi r=cap lam S r)
    (hcapScore : phi c=capScore lam S c)
    (hcontact : curvePrimitive phi t=quadratic lam t-S)
    (hend : curvePrimitive phi z0=quadratic lam z0-S)
    (htzero : scoreDefect phi lam t=0)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c t))
    (hslope : ∀ a ∈ Icc c t,∀ b ∈ Icc c t,a≤b →
      scoreDefect phi lam a-scoreDefect phi lam b≤k*(b-a)) :
    ∀ r ∈ Icc (0:ℝ) z0,binaryAreaLower lam S (phi 0) slope xh c t k r≤
      binarySlackArea phi lam S r := by
  have hc0 := hxh.trans hxc
  have hJc := hcapJ c ⟨hxc,le_rfl⟩
  have hsc : scoreDefect phi lam c=capSlack lam S c := by
    unfold scoreDefect capSlack
    rw [hcapScore]
  intro r hr
  by_cases hrh : r≤xh
  · rw [binaryAreaLower,if_pos hrh,binarySlackArea,
      h.affine_head_primitive hhead ⟨hr.1,hrh⟩]
  · by_cases hrc : r≤c
    · rw [binaryAreaLower,if_neg hrh,if_pos hrc,binarySlackArea,
        hcapJ r ⟨le_of_not_ge hrh,hrc⟩]
      unfold capDeficit
      linarith
    · by_cases hrt : r≤t
      · rw [binaryAreaLower,if_neg hrh,if_neg hrc,if_pos hrt]
        have hh := h.primitive_slack_lower hc0 (htz.trans hz1) ⟨le_of_not_ge hrc,hrt⟩ hk
          (by simpa only [hsc] using hs) hcontact htzero hanti hslope
        dsimp only at hh
        rw [hsc,hJc] at hh
        convert! hh using 1 <;> simp only [binaryAreaCone,binaryAreaCutoff,capDeficit,binarySlackArea] <;> ring
      · rw [binaryAreaLower,if_neg hrh,if_neg hrc,if_neg hrt]
        have hh := h.binarySlackArea_antitone S ⟨hr.1,hr.2.trans hz1⟩
          ⟨hr.1.trans hr.2,hz1⟩ hr.2
        have he : binarySlackArea phi lam S z0=0 := by unfold binarySlackArea; rw [hend]; ring
        simpa only [he] using hh

/-- C.19 and the exact head/cap scores give a genuine pointwise lower score
profile. Finite right sums of this profile therefore bound actual integrals. -/
theorem binaryScoreLower_le {S slope xh c t z0 k : ℝ}
    (hxh : 0≤xh) (hxc : xh≤c) (hct : c≤t) (htz : t≤z0) (hz1 : z0≤1)
    (hk : 0<k) (hs : 0<capSlack lam S c)
    (hhead : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hcapJ : curvePrimitive phi c=cap lam S c)
    (hcapScore : ∀ r ∈ Icc xh c,phi r=capScore lam S r)
    (hcontact : curvePrimitive phi t=quadratic lam t-S)
    (hanti : AntitoneOn (scoreDefect phi lam) (Icc c t))
    (hslope : ∀ a ∈ Icc c t,∀ b ∈ Icc c t,a≤b →
      scoreDefect phi lam a-scoreDefect phi lam b≤k*(b-a)) :
    ∀ r ∈ Icc (0:ℝ) z0,binaryScoreLower lam S (phi 0) slope xh c t k r≤scoreDefect phi lam r := by
  have hc0 := hxh.trans hxc
  have hsc : scoreDefect phi lam c=capSlack lam S c := by
    unfold scoreDefect capSlack
    rw [hcapScore c ⟨hxc,le_rfl⟩]
  intro r hr
  by_cases hrh : r≤xh
  · rw [binaryScoreLower,if_pos hrh,scoreDefect,hhead r ⟨hr.1,hrh⟩]
  · by_cases hrc : r≤c
    · rw [binaryScoreLower,if_neg hrh,if_pos hrc,scoreDefect,
        hcapScore r ⟨le_of_not_ge hrh,hrc⟩]
      exact le_rfl
    · by_cases hrt : r≤t
      · rw [binaryScoreLower,if_neg hrh,if_neg hrc,if_pos hrt]
        have hh := h.score_slack_lower hc0 (htz.trans hz1) ⟨le_of_not_ge hrc,hrt⟩ hk
          (by simpa only [hsc] using hs) hcontact hanti
          (fun u hu => hslope u ⟨hu.1,hu.2.trans hrt⟩ r ⟨le_of_not_ge hrc,hrt⟩ hu.2)
        dsimp only at hh
        rw [hsc,hcapJ] at hh
        convert! hh using 1 <;> simp only [binaryScoreCone,binaryAreaCutoff,capDeficit] <;> ring
      · rw [binaryScoreLower,if_neg hrh,if_neg hrc,if_neg hrt]
        exact h.scoreDefect_nonneg ⟨hr.1,hr.2.trans hz1⟩

/-- The upper area profile is obtained from exact primitive formulas followed
by a proved integral estimate from the actual reference-rank bounds. -/
theorem binaryAreaUpperProfile_ge {S slope xh c z0 k pref epsArea epsScore : ℝ}
    (hxh : 0≤xh) (hxc : xh≤c) (hz1 : z0≤1) (hpref : pref ∈ Icc c z0)
    (hhead : ∀ r ∈ Icc (0:ℝ) xh,phi r=phi 0+slope*r)
    (hcapJ : ∀ r ∈ Icc xh c,curvePrimitive phi r=cap lam S r)
    (harea : binarySlackArea phi lam S pref≤epsArea)
    (hscore : scoreDefect phi lam pref≤epsScore)
    (hfall : ∀ r ∈ Icc c pref,scoreDefect phi lam r-scoreDefect phi lam pref≤k*(pref-r)) :
    ∀ r ∈ Icc (0:ℝ) z0,binarySlackArea phi lam S r≤
      binaryAreaUpperProfile lam S (phi 0) slope xh c k pref epsArea epsScore r := by
  intro r hr
  by_cases hrh : r≤xh
  · rw [binaryAreaUpperProfile,if_pos hrh,binarySlackArea,
      h.affine_head_primitive hhead ⟨hr.1,hrh⟩]
  · by_cases hrc : r≤c
    · rw [binaryAreaUpperProfile,if_neg hrh,if_pos hrc,binarySlackArea,
        hcapJ r ⟨le_of_not_ge hrh,hrc⟩]
      unfold capDeficit
      linarith
    · rw [binaryAreaUpperProfile,if_neg hrh,if_neg hrc]
      exact h.binarySlackArea_upper (hxh.trans hxc) hz1 hpref harea hscore hfall r
        ⟨le_of_not_ge hrc,hr.2⟩

end VerifierCurve
end OptimalG
