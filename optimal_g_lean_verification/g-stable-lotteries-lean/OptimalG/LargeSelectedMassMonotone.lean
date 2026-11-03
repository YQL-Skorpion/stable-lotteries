import OptimalG.LargeSelectedPiecewise
import OptimalG.LargeSelectedEnvelopeBounds
import OptimalG.Certificates.LargeSelectedExpressions
import OptimalG.RationalStationaryCurve

namespace OptimalG
open Set Variational Certificates.LargeSelectedExpressions

structure LargeSelectedDerivativeSigns (lam S : ℝ) : Prop where
  head : ∀ p∈Icc (13/20:ℝ) (7/8),headMassDerivative lam S p≤0
  middle : ∀ p∈Icc (13/20:ℝ) (7/8),middleMassDerivative lam S p≤0
  late : ∀ p∈Icc (13/20:ℝ) (7/8),lateMassDerivative lam S p≤0
  flat : capDeficit lam S (313/1000)≤3/10000

namespace BinaryCurveGeometry
variable {phi : ℝ→ℝ} {lam S c : ℝ}
    (g : BinaryCurveGeometry phi lam S (Certificates.SmallMassExpressions.slope lam S) c)
include g

theorem largeSelected_mass_antitone (h : VerifierCurve phi lam)
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hi : phi 0=Certificates.SmallMassExpressions.initial lam S)
    {z q e : ℝ} (hz : z∈Icc (391/500:ℝ) (7/8)) (hq : q∈Icc (0:ℝ) lam)
    (he : e≤13/200) (hn : LargeSelectedDerivativeSigns lam S) :
    AntitoneOn (largeSelectedNumerator lam S z q e
      (largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S) q)
      (largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
        (Certificates.SmallMassExpressions.slope lam S))) (Icc (13/20:ℝ) z) := by
  let U := largeRemainingUpper lam S (Certificates.SmallMassExpressions.initial lam S)
    (Certificates.SmallMassExpressions.slope lam S)
  let L := largeRemainingLower lam S (Certificates.SmallMassExpressions.initial lam S)
    (Certificates.SmallMassExpressions.slope lam S) q
  have hL : lam∈Icc (22493/40000:ℝ) (56233/100000) := by
    constructor <;> linarith only [g.lambda_mem.1,g.lambda_mem.2]
  have hgap := g.largeSelected_initial_gap hS hi
  have hlow : 0≤L := g.largeSelected_lower_nonneg h hi hq
  have hder (p V d : ℝ) (hp : p∈Icc (13/20:ℝ) z)
      (hV : V≤S) (hC : -d≤lam-Certificates.SmallMassExpressions.initial lam S)
      (hmid : 527/2000<q→-d≤1/20)
      (hlate : 9/25<q→V≤3/10000 ∧ d=0) :
      largeSelectedMassDerivative lam S p z q e V L d≤0 := by
    have hp0 : 0≤p := by linarith only [hp.1]
    have hlp : lam≤p := by linarith only [hL.2,hp.1]
    have hneg : 7/8-lam-p≤0 := by linarith only [hL.1,hp.1]
    have hpall : p∈Icc (13/20:ℝ) (7/8) := ⟨hp.1,hp.2.trans hz.2⟩
    by_cases hqh : q≤527/2000
    · exact (largeSelectedMassDerivative_le hp0 hlp (by linarith only [hp.1]) hqh hz hneg
        hV hlow hC he).trans (hn.head p hpall)
    · by_cases hqm : q≤9/25
      · exact (largeSelectedMassDerivative_le hp0 hlp (by linarith only [hp.1]) hqm hz hneg
          hV hlow (hmid (lt_of_not_ge hqh)) he).trans (hn.middle p hpall)
      · obtain ⟨hsmall,hd⟩ := hlate (lt_of_not_ge hqm)
        exact (largeSelectedMassDerivative_le hp0 hlp hlp hq.2 hz hneg hsmall hlow
          (by rw [hd];norm_num : -d≤0) he).trans (hn.late p hpall)
  have hrange {p : ℝ} (hp : p∈Icc (13/20:ℝ) z) : z-p+q∈Icc (0:ℝ) 1 :=
    ⟨by linarith only [hp.2,hq.1],by linarith only [hz.2,hp.1,hq.2,hL.2]⟩
  have hqdelay {p : ℝ} (hp : p∈Icc (13/20:ℝ) z) : q≤z-p+q := by linarith only [hp.2]
  let a := z+q-313/1000
  let b := z+q-527/2000
  apply antitoneOn_interval_split (c:=a)
  · have hdom {p : ℝ} (hp : p∈Icc (13/20:ℝ) (min z a)) : p∈Icc (13/20:ℝ) z :=
      ⟨hp.1,(le_min_iff.mp hp.2).1⟩
    have hflat {p : ℝ} (hp : p∈Icc (13/20:ℝ) (min z a)) : 313/1000≤z-p+q := by
      have hh := (le_min_iff.mp hp.2).2
      dsimp [a] at hh
      linarith only [hh]
    have hanti := largeSelected_branch_antitone (lam:=lam) (S:=S) (z:=z) (q:=q) (e:=e) (lower:=L)
      (upper:=fun _=>capDeficit lam S (313/1000)) (du:=fun _=>0)
      (a:=13/20) (b:=min z a) (fun p _=>hasDerivAt_const (z-p+q) _)
      (fun p hp=>hder p _ 0 (hdom hp)
        (largeSelected_capDeficit_le_area hL hS ⟨by norm_num,le_rfl⟩)
        (by linarith only [hgap]) (fun _=>by norm_num) (fun _=>⟨hn.flat,rfl⟩))
    intro x hx y hy hxy
    have hh := hanti hx hy hxy
    simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_flat (hflat hx),
      largeRemainingUpper_eq_flat (hflat hy)] using hh
  · apply antitoneOn_interval_split (c:=b)
    · have hdom {p : ℝ} (hp : p∈Icc (max (13/20) a) (min z b)) : p∈Icc (13/20:ℝ) z :=
        ⟨(le_max_left _ _).trans hp.1,(le_min_iff.mp hp.2).1⟩
      have hcap {p : ℝ} (hp : p∈Icc (max (13/20) a) (min z b)) :
          z-p+q∈Icc (527/2000:ℝ) (313/1000) := by
        have ha := (le_max_right _ _).trans hp.1
        have hb := (le_min_iff.mp hp.2).2
        dsimp [a,b] at ha hb
        constructor <;> linarith only [ha,hb]
      have hanti := largeSelected_branch_antitone (lam:=lam) (S:=S) (z:=z) (q:=q) (e:=e) (lower:=L)
        (upper:=capDeficit lam S) (du:=fun r=> -capSlack lam S r)
        (a:=max (13/20) a) (b:=min z b)
        (fun p hp=>capDeficit_hasDerivAt lam S (z-p+q) (by linarith only [(hcap hp).2]))
        (by
          intro p hp
          have hs := largeSelected_capSlack_upper hL hS (hcap hp)
          apply hder p _ _ (hdom hp) (largeSelected_capDeficit_le_area hL hS (hcap hp))
          · linarith only [hs,hgap]
          · intro _;linarith only [hs]
          · intro hq36
            exfalso
            have hh := hqdelay (hdom hp)
            linarith only [hq36,hh,(hcap hp).2])
      intro x hx y hy hxy
      have hh := hanti hx hy hxy
      simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_cap (hcap hx),
        largeRemainingUpper_eq_cap (hcap hy)] using hh
    · have hdom {p : ℝ} (hp : p∈Icc (max (max (13/20) a) b) z) : p∈Icc (13/20:ℝ) z :=
        ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hp.1),hp.2⟩
      have hhead {p : ℝ} (hp : p∈Icc (max (max (13/20) a) b) z) : z-p+q≤527/2000 := by
        have hh := (le_max_right _ _).trans hp.1
        dsimp [b] at hh
        linarith only [hh]
      have hanti := largeSelected_branch_antitone (lam:=lam) (S:=S) (z:=z) (q:=q) (e:=e) (lower:=L)
        (upper:=largeHeadRemaining lam S)
        (du:=fun r=>Certificates.SmallMassExpressions.initial lam S-lam+
          (1+Certificates.SmallMassExpressions.slope lam S)*r)
        (a:=max (max (13/20) a) b) (b:=z) (fun p _=>largeHeadRemaining_hasDerivAt lam S (z-p+q))
        (by
          intro p hp
          have hu := g.largeSelected_upper_le_area h hS hi (hrange (hdom hp))
          rw [largeRemainingUpper_eq_head (hhead hp)] at hu
          apply hder p _ _ (hdom hp) hu
          · have hm := mul_nonneg
              (show 0≤1+Certificates.SmallMassExpressions.slope lam S by linarith only [g.head_slope])
              (hrange (hdom hp)).1
            linarith only [hm]
          · intro hqh
            exfalso
            have hh := hqdelay (hdom hp)
            linarith only [hqh,hh,hhead hp]
          · intro hq36
            exfalso
            have hh := hqdelay (hdom hp)
            linarith only [hq36,hh,hhead hp])
      intro x hx y hy hxy
      have hh := hanti hx hy hxy
      simpa only [largeSelectedNumerator,U,largeRemainingUpper_eq_head (hhead hx),
        largeRemainingUpper_eq_head (hhead hy)] using hh

end BinaryCurveGeometry
end OptimalG
