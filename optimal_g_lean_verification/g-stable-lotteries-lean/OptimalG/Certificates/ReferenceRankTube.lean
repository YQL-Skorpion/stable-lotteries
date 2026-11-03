import OptimalG.Certificates.ReferenceProfileCertificate
import OptimalG.VariationalRankTube

/-! Matched ranks are certified by cap and quadratic endpoint inequalities.
The proposed endpoints may originate from an approximate inverse, but the
checker and its proof use only the actual rational obstacle expressions. -/
namespace OptimalG.Certificates
open Set RatExpr

structure ReferenceRankTube where
  lam : ℚ
  referenceSlack : ℚ
  leftContact : ℚ
  rightContact : ℚ
  lo : ℚ
  hi : ℚ
  input : Fin 3→IntegerInterval

namespace ReferenceRankTube

def lowGap (c : ReferenceRankTube) : RatExpr 3 :=
  .var 1-.const (ReferenceProfileBox.capValue c.lam c.referenceSlack c.lo)+
    (.var 0-.const c.referenceSlack)*(.var 2+.const (c.lam/(1-c.lo)))

def highGap (c : ReferenceRankTube) : RatExpr 3 :=
  .const (c.lam*c.hi-c.hi*c.hi/2-c.referenceSlack)-.var 1-
    (.var 0-.const c.referenceSlack)*(1+.var 2)

theorem lowGap_eval (c : ReferenceRankTube) (S F u : ℝ) :
    c.lowGap.eval ![S,F,u]=F+(S-c.referenceSlack)*u-cap c.lam S c.lo := by
  simp [lowGap,eval,ReferenceProfileBox.capValue,cap,div_eq_mul_inv]
  ring

theorem highGap_eval (c : ReferenceRankTube) (S F u : ℝ) :
    c.highGap.eval ![S,F,u]=quadratic c.lam c.hi-S-(F+(S-c.referenceSlack)*u) := by
  simp [highGap,eval,quadratic]
  ring

def check (s k : ℕ) (c : ReferenceRankTube) : Bool :=
  decide (c.lo≤c.rightContact ∧ c.leftContact≤c.hi ∧ c.lo≤c.hi) &&
  ((if c.lo≤c.leftContact then true else
      c.lowGap.enclosureRefinedCheck s k c.input ⟨0,s⟩) &&
   (if c.rightContact≤c.hi then true else
      c.highGap.enclosureRefinedCheck s k c.input ⟨0,s⟩))

theorem checked_rank_bounds {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceRankTube) (hc : c.check s k=true)
    {d : Variational.LowRankData} (hd : Variational.Admissible c.lam d)
    {r F u : ℝ}
    (hleft : Variational.ell≤(c.leftContact:ℝ))
    (hright : (c.rightContact:ℝ)≤Variational.tEnd)
    (hr : r∈Icc (c.leftContact:ℝ) c.rightContact)
    (hinput : ∀ i,(c.input i).Contains s (![d.S,F,u] i))
    (hcap : F+(d.S-c.referenceSlack)*u≤cap c.lam d.S r)
    (hquad : quadratic c.lam r-d.S≤F+(d.S-c.referenceSlack)*u) :
    r∈Icc (c.lo:ℝ) c.hi := by
  obtain ⟨hgeom,hchecks⟩ := Bool.and_eq_true_iff.mp hc
  have hg : c.lo≤c.rightContact ∧ c.leftContact≤c.hi ∧ c.lo≤c.hi :=
    of_decide_eq_true hgeom
  obtain ⟨hlow,hhigh⟩ := Bool.and_eq_true_iff.mp hchecks
  have hr' : r∈Icc Variational.ell Variational.tEnd :=
    ⟨hleft.trans hr.1,hr.2.trans hright⟩
  constructor
  · by_cases he : c.lo≤c.leftContact
    · exact (show (c.lo:ℝ)≤c.leftContact by exact_mod_cast he).trans hr.1
    · rw [if_neg he] at hlow
      have hv := RatExpr.enclosureRefinedCheck_sound hs hk c.lowGap c.input ⟨0,s⟩ hlow _ hinput
      rw [c.lowGap_eval] at hv
      have hnonneg : 0≤F+(d.S-c.referenceSlack)*u-cap c.lam d.S c.lo := by
        exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hv.1)
          (show (0:ℝ)<s by exact_mod_cast hs)
      apply hd.rank_lower_of_cap_endpoint
        ⟨hleft.trans (show (c.leftContact:ℝ)≤c.lo by exact_mod_cast (le_of_not_ge he)),
          (show (c.lo:ℝ)≤c.rightContact by exact_mod_cast hg.1).trans hright⟩ hr' hcap
      exact sub_nonneg.mp hnonneg
  · by_cases he : c.rightContact≤c.hi
    · exact hr.2.trans (show (c.rightContact:ℝ)≤c.hi by exact_mod_cast he)
    · rw [if_neg he] at hhigh
      have hv := RatExpr.enclosureRefinedCheck_sound hs hk c.highGap c.input ⟨0,s⟩ hhigh _ hinput
      rw [c.highGap_eval] at hv
      have hnonneg : 0≤quadratic c.lam c.hi-d.S-(F+(d.S-c.referenceSlack)*u) := by
        exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hv.1)
          (show (0:ℝ)<s by exact_mod_cast hs)
      apply hd.rank_upper_of_quadratic_endpoint
        ⟨hleft.trans (show (c.leftContact:ℝ)≤c.hi by exact_mod_cast hg.2.1),
          (show (c.hi:ℝ)≤c.rightContact by exact_mod_cast (le_of_not_ge he)).trans hright⟩
        hr' hquad
      exact sub_nonneg.mp hnonneg

end ReferenceRankTube
end OptimalG.Certificates
