import OptimalG.IntervalGlue

/-! Finite increment bounds glue at a common endpoint without requiring
differentiability of the score at the join. -/
namespace OptimalG.Variational
open Set

theorem lower_increment_glue {f : ℝ → ℝ} {a c b m : ℝ}
    (hac : a≤c) (hcb : c≤b)
    (hl : ∀ r∈Icc a c,∀ s∈Icc a c,r≤s → m*(s-r)≤f s-f r)
    (hr : ∀ r∈Icc c b,∀ s∈Icc c b,r≤s → m*(s-r)≤f s-f r) :
    ∀ r∈Icc a b,∀ s∈Icc a b,r≤s → m*(s-r)≤f s-f r := by
  intro r hrr s hss hrs
  by_cases hsc : s≤c
  · exact hl r ⟨hrr.1,hrs.trans hsc⟩ s ⟨hss.1,hsc⟩ hrs
  · by_cases hrc : r≤c
    · have h1 := hl r ⟨hrr.1,hrc⟩ c ⟨hac,le_rfl⟩ hrc
      have h2 := hr c ⟨le_rfl,hcb⟩ s ⟨le_of_not_ge hsc,hss.2⟩ (le_of_not_ge hsc)
      nlinarith only [h1,h2]
    · exact hr r ⟨le_of_not_ge hrc,hrr.2⟩ s ⟨(le_of_not_ge hrc).trans hrs,hss.2⟩ hrs

theorem upper_increment_glue {f : ℝ → ℝ} {a c b m : ℝ}
    (hac : a≤c) (hcb : c≤b)
    (hl : ∀ r∈Icc a c,∀ s∈Icc a c,r≤s → f s-f r≤m*(s-r))
    (hr : ∀ r∈Icc c b,∀ s∈Icc c b,r≤s → f s-f r≤m*(s-r)) :
    ∀ r∈Icc a b,∀ s∈Icc a b,r≤s → f s-f r≤m*(s-r) := by
  have hh := lower_increment_glue (f:=fun r => -f r) (m:= -m) hac hcb
    (fun r hrr s hss hrs => by have h := hl r hrr s hss hrs; nlinarith only [h])
    (fun r hrr s hss hrs => by have h := hr r hrr s hss hrs; nlinarith only [h])
  intro r hrr s hss hrs
  have h := hh r hrr s hss hrs
  nlinarith only [h]

end OptimalG.Variational
