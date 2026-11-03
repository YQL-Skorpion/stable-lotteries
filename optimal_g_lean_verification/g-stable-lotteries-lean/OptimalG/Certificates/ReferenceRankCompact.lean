import OptimalG.Certificates.ReferenceRankCell
import OptimalG.Certificates.Compact

/-! Rank endpoint enclosure uses only the compact parameter rectangle and
the primitive obstacles. A transferred competitor need not be normalized
as an admissible low-rank datum at the reference parameter. -/
namespace OptimalG.Certificates
open Set

theorem compact_cap_strictMono {L S : ℝ} (hL : Compact.LambdaRange L)
    (hS : S≤(3:ℝ)/100) : StrictMonoOn (cap L S) (Icc Variational.ell Variational.tEnd) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (Variational.cap_continuous_lowInterval L S)
  intro r hr
  have hr' := interior_subset hr
  have hr1 : r≤(385:ℝ)/1000 := hr'.2
  have hL0 : 0<L := by have hh:=hL.1; norm_num [Compact.LambdaRange] at hh; linarith
  have hden : 0<(1-r)^2 := sq_pos_of_pos (by linarith)
  have hfrac : S/(1-r)^2<(1:ℝ)/2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [sq_nonneg (r-385/1000)]
  rw [(Variational.cap_hasDerivAt L S r (by linarith)).deriv]
  unfold Variational.capScore
  rw [mul_div_assoc]
  nlinarith [mul_pos hL0 (sub_pos.mpr hfrac)]

theorem compact_quadratic_strictMono {L : ℝ} (hL : Compact.LambdaRange L) :
    StrictMonoOn (quadratic L) (Icc Variational.ell Variational.tEnd) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by unfold quadratic; fun_prop)
  intro r hr
  change 0 < deriv (Variational.quadratic L) r
  rw [(Variational.quadratic_hasDerivAt L r).deriv]
  have hr' := (interior_subset hr).2
  have hl := hL.1
  norm_num [Compact.LambdaRange,Variational.tEnd] at hl hr'
  linarith

namespace ReferenceRankTube

theorem checked_rank_bounds_compact {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceRankTube) (hc : c.check s k=true)
    {S r F u : ℝ} (hL : Compact.LambdaRange c.lam) (hS : S≤(3:ℝ)/100)
    (hleft : Variational.ell≤(c.leftContact:ℝ))
    (hright : (c.rightContact:ℝ)≤Variational.tEnd)
    (hr : r∈Icc (c.leftContact:ℝ) c.rightContact)
    (hinput : ∀ i,(c.input i).Contains s (![S,F,u] i))
    (hcap : F+(S-c.referenceSlack)*u≤cap c.lam S r)
    (hquad : quadratic c.lam r-S≤F+(S-c.referenceSlack)*u) :
    r∈Icc (c.lo:ℝ) c.hi := by
  obtain ⟨hgeom,hchecks⟩ := Bool.and_eq_true_iff.mp hc
  have hg : c.lo≤c.rightContact ∧ c.leftContact≤c.hi ∧ c.lo≤c.hi := of_decide_eq_true hgeom
  obtain ⟨hlow,hhigh⟩ := Bool.and_eq_true_iff.mp hchecks
  have hr' : r∈Icc Variational.ell Variational.tEnd :=
    ⟨hleft.trans hr.1,hr.2.trans hright⟩
  constructor
  · by_cases he : c.lo≤c.leftContact
    · exact (show (c.lo:ℝ)≤c.leftContact by exact_mod_cast he).trans hr.1
    · rw [if_neg he] at hlow
      have hv := RatExpr.enclosureRefinedCheck_sound hs hk c.lowGap c.input ⟨0,s⟩ hlow _ hinput
      rw [c.lowGap_eval] at hv
      have hnonneg : 0≤F+(S-c.referenceSlack)*u-cap c.lam S c.lo :=
        nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hv.1) (by exact_mod_cast hs)
      have hlo : (c.lo:ℝ)∈Icc Variational.ell Variational.tEnd :=
        ⟨hleft.trans (by exact_mod_cast (le_of_not_ge he)),
          (show (c.lo:ℝ)≤c.rightContact by exact_mod_cast hg.1).trans hright⟩
      by_contra hn
      have hh := compact_cap_strictMono hL hS hr' hlo (lt_of_not_ge hn)
      linarith
  · by_cases he : c.rightContact≤c.hi
    · exact hr.2.trans (show (c.rightContact:ℝ)≤c.hi by exact_mod_cast he)
    · rw [if_neg he] at hhigh
      have hv := RatExpr.enclosureRefinedCheck_sound hs hk c.highGap c.input ⟨0,s⟩ hhigh _ hinput
      rw [c.highGap_eval] at hv
      have hnonneg : 0≤quadratic c.lam c.hi-S-(F+(S-c.referenceSlack)*u) :=
        nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hv.1) (by exact_mod_cast hs)
      have hhi : (c.hi:ℝ)∈Icc Variational.ell Variational.tEnd :=
        ⟨hleft.trans (by exact_mod_cast hg.2.1),
          (show (c.hi:ℝ)≤c.rightContact by exact_mod_cast (le_of_not_ge he)).trans hright⟩
      by_contra hn
      have hh := compact_quadratic_strictMono hL hhi hr' (lt_of_not_ge hn)
      linarith

end ReferenceRankTube
namespace ReferenceRankCell

theorem checked_contains_compact {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceRankCell) (hc : c.check s k=true)
    {S r F u : ℝ} (hL : Compact.LambdaRange c.tube.lam) (hS : S≤(3:ℝ)/100)
    (hleft : Variational.ell≤(c.tube.leftContact:ℝ))
    (hright : (c.tube.rightContact:ℝ)≤Variational.tEnd)
    (hinput : ∀ i,(c.tube.input i).Contains s (![S,F,u] i))
    (hactual : if c.matched then
      r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
      F+(S-c.tube.referenceSlack)*u≤cap c.tube.lam S r ∧
      quadratic c.tube.lam r-S≤F+(S-c.tube.referenceSlack)*u
      else r∈Icc (c.referenceLo:ℝ) c.referenceHi) : c.bounds.Contains s r := by
  obtain ⟨hgeom,hrest⟩ := Bool.and_eq_true_iff.mp hc
  have hg : c.tube.lo=(c.bounds.lo:ℚ)/(s:ℚ) ∧
      c.tube.hi=(c.bounds.hi:ℚ)/(s:ℚ) := of_decide_eq_true hgeom
  obtain ⟨hreference,htube⟩ := Bool.and_eq_true_iff.mp hrest
  cases hm : c.matched with
  | false =>
    exact IntegerInterval.rationalEndpointsCheck_sound hreference (by simpa [hm] using hactual)
  | true =>
    have ha : r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
        F+(S-c.tube.referenceSlack)*u≤cap c.tube.lam S r ∧
        quadratic c.tube.lam r-S≤F+(S-c.tube.referenceSlack)*u := by
      simpa [hm] using hactual
    have hh := c.tube.checked_rank_bounds_compact hs hk (by simpa [hm] using htube)
      hL hS hleft hright ha.1 hinput ha.2.1 ha.2.2
    apply (IntegerInterval.contains_iff hs c.bounds r).mpr
    simpa only [hg.1,hg.2,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,mem_Icc,
      IntegerInterval.toRat,RatInterval.Contains] using hh

end ReferenceRankCell
end OptimalG.Certificates
