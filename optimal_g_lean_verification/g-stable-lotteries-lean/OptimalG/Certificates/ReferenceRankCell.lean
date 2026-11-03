import OptimalG.Certificates.ReferenceRankOrder

/-! Each rank is either unchanged on the cap prefix or matched through the
actual low primitive. Both cases yield the same integer interval conclusion. -/
namespace OptimalG.Certificates
open Set

structure ReferenceRankCell where
  tube : ReferenceRankTube
  matched : Bool
  referenceLo : ℚ
  referenceHi : ℚ
  bounds : IntegerInterval

namespace ReferenceRankCell

def check (s k : ℕ) (c : ReferenceRankCell) : Bool :=
  decide (c.tube.lo=(c.bounds.lo:ℚ)/(s:ℚ) ∧ c.tube.hi=(c.bounds.hi:ℚ)/(s:ℚ)) &&
  (IntegerInterval.rationalEndpointsCheck s c.referenceLo c.referenceHi c.bounds &&
   if c.matched then c.tube.check s k else true)

theorem checked_contains {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceRankCell) (hc : c.check s k=true)
    {d : Variational.LowRankData} (hd : Variational.Admissible c.tube.lam d)
    {r F u : ℝ}
    (hleft : Variational.ell≤(c.tube.leftContact:ℝ))
    (hright : (c.tube.rightContact:ℝ)≤Variational.tEnd)
    (hinput : ∀ i,(c.tube.input i).Contains s (![d.S,F,u] i))
    (hactual : if c.matched then
      r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
      F+(d.S-c.tube.referenceSlack)*u≤cap c.tube.lam d.S r ∧
      quadratic c.tube.lam r-d.S≤F+(d.S-c.tube.referenceSlack)*u
      else r∈Icc (c.referenceLo:ℝ) c.referenceHi) :
    c.bounds.Contains s r := by
  obtain ⟨hgeom,hrest⟩ := Bool.and_eq_true_iff.mp hc
  have hg : c.tube.lo=(c.bounds.lo:ℚ)/(s:ℚ) ∧
      c.tube.hi=(c.bounds.hi:ℚ)/(s:ℚ) := of_decide_eq_true hgeom
  obtain ⟨hreference,htube⟩ := Bool.and_eq_true_iff.mp hrest
  cases hm : c.matched with
  | false =>
    exact IntegerInterval.rationalEndpointsCheck_sound hreference (by simpa [hm] using hactual)
  | true =>
    have ha : r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
        F+(d.S-c.tube.referenceSlack)*u≤cap c.tube.lam d.S r ∧
        quadratic c.tube.lam r-d.S≤F+(d.S-c.tube.referenceSlack)*u := by
      simpa [hm] using hactual
    have hh := c.tube.checked_rank_bounds hs hk (by simpa [hm] using htube)
      hd hleft hright ha.1 hinput ha.2.1 ha.2.2
    apply (IntegerInterval.contains_iff hs c.bounds r).mpr
    simpa only [hg.1,hg.2,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,mem_Icc,IntegerInterval.toRat,RatInterval.Contains] using hh

end ReferenceRankCell
end OptimalG.Certificates
