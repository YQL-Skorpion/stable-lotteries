import OptimalG.Certificates.ReferenceRankCell
import OptimalG.VariationalPrimitive

/-! Match identities turn the admissible primitive obstacles into the exact
two endpoint inequalities consumed by the rank enclosure checker. -/
namespace OptimalG.Certificates.ReferenceRankCell
open Set

theorem checked_contains_of_match {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceRankCell) (hc : c.check s k=true)
    {d : Variational.LowRankData} (hd : Variational.Admissible c.tube.lam d)
    {r F u : ℝ}
    (hleft : Variational.ell≤(c.tube.leftContact:ℝ))
    (hright : (c.tube.rightContact:ℝ)≤Variational.tEnd)
    (hinput : ∀ i,(c.tube.input i).Contains s (![d.S,F,u] i))
    (hmatch : if c.matched then
      r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
        Variational.lowPrimitive c.tube.lam d r=F+(d.S-c.tube.referenceSlack)*u
      else r∈Icc (c.referenceLo:ℝ) c.referenceHi) : c.bounds.Contains s r := by
  apply c.checked_contains hs hk hc hd hleft hright hinput
  cases hm : c.matched with
  | false => simpa [hm] using hmatch
  | true =>
    have hh : r∈Icc (c.tube.leftContact:ℝ) c.tube.rightContact ∧
        Variational.lowPrimitive c.tube.lam d r=F+(d.S-c.tube.referenceSlack)*u := by
      simpa [hm] using hmatch
    have hr : r∈Icc Variational.ell Variational.tEnd :=
      ⟨hleft.trans hh.1.1,hh.1.2.trans hright⟩
    have hcap := hd.lowPrimitive_le_cap hr
    have hquad := hd.lowPrimitive_lower hr
    rw [hh.2] at hcap hquad
    simpa [hm] using And.intro hh.1 (And.intro hcap hquad)

end OptimalG.Certificates.ReferenceRankCell
