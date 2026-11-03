import OptimalG.VariationalCapFlow
import OptimalG.VariationalRegularPositive

/-! An actual minimizing datum can be normalized to the cap before its final
contact, retaining feasibility and a positive Lipschitz score representative
after that contact. No numerical localization assumptions are hidden here. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem capReplacement_last_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Icc ell tEnd)
    (hcontact : lowPrimitive lam d c = cap lam d.S c)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c) :
    ∀ r ∈ Icc ell tEnd,
      lowPrimitive lam (capReplacement lam d c) r = cap lam (capReplacement lam d c).S r → r ≤ c := by
  intro r hr heq
  by_cases hrc : r ≤ c
  · exact hrc
  · rw [lowPrimitive_capReplacement_after hd hc hcontact ⟨(lt_of_not_ge hrc).le,hr.2⟩] at heq
    exact hlast r hr heq

/-- Exact cap normalization of an interior minimizing feasible pair. -/
theorem minimizer_cap_normalization {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d)) :
    ∃ c ∈ Ico xLo xHi, ∃ d' : LowRankData,
      d'.S = d.S ∧ Admissible lam d' ∧ PassesTerminalTests lam d' (continuation lam d') ∧
      (∀ r ∈ Icc ell c, lowPrimitive lam d' r = cap lam d'.S r) ∧
      (∀ r ∈ Icc c tEnd, lowPrimitive lam d' r = lowPrimitive lam d r) ∧
      (∀ r ∈ Icc ell tEnd, lowPrimitive lam d' r = cap lam d'.S r → r ≤ c) := by
  obtain ⟨c,hc,hcontact,hlast⟩ := hd.exists_last_cap_contact
  have hcx := minimizer_last_contact_in_test_interval hd hl hmin hpass hc hcontact hlast
  have hci : c ∈ Ioc ell tEnd :=
    ⟨(by norm_num [ell,xLo] : ell < xLo).trans_le hcx.1,hc.2⟩
  refine ⟨c,hcx,capReplacement lam d c,rfl,capReplacement_admissible hd hci hcontact,
    capReplacement_passesTerminalTests hd hci hcx.2.le hcontact hpass,?_,?_,?_⟩
  · intro r hr
    exact lowPrimitive_capReplacement_before hd hc.2 hr
  · intro r hr
    exact lowPrimitive_capReplacement_after hd hc hcontact hr
  · exact capReplacement_last_contact hd hc hcontact hlast

/-- The normalized minimizer has a genuine positive, nonincreasing Lipschitz
score on the entire closed free interval. The cap and tail junction conditions
beyond this interval are separate analytic obligations. -/
theorem minimizer_cap_regular_data {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d)) :
    ∃ c ∈ Ico xLo xHi, ∃ d' : LowRankData, ∃ L : ℝ≥0, ∃ ψ : ℝ → ℝ,
      d'.S = d.S ∧ Admissible lam d' ∧ PassesTerminalTests lam d' (continuation lam d') ∧
      (∀ r ∈ Icc ell c, lowPrimitive lam d' r = cap lam d'.S r) ∧
      (∀ r ∈ Icc ell tEnd, lowPrimitive lam d' r = cap lam d'.S r → r ≤ c) ∧
      LipschitzWith L ψ ∧ AntitoneOn ψ (Icc c xHi) ∧
      d'.phi =ᵐ[volume.restrict (Icc c xHi)] ψ ∧
      (∀ r ∈ Icc c xHi, (7:ℝ)/100 ≤ ψ r ∧ ψ r ≤ lam-r) ∧
      (∀ r ∈ Icc c xHi, lowPrimitive lam d' r = cap lam d'.S c+∫ t in c..r,ψ t) := by
  obtain ⟨c,hc,d',hS,hd',hpass',hcap,_,hlast⟩ := minimizer_cap_normalization hd hl hmin hpass
  have hce : ell ≤ c := (by norm_num [ell,xLo] : ell ≤ xLo).trans hc.1
  have hct : c ≤ tEnd := hc.2.le.trans (by norm_num [xHi,tEnd])
  have hcontact := hcap c ⟨hce,le_rfl⟩
  obtain ⟨_,L,ψ,hψ,hm,heq,hgraph,hbounds,hprimitive⟩ :=
    minimizer_regular_interval hd' hl hmin hpass' ⟨hce,hct⟩ hcontact hlast
  have heq' : d'.phi =ᵐ[volume.restrict (Ioo c xHi)] ψ :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq
  have hpos := minimizer_continuous_rep_positive hd' hl hmin hpass' ⟨hce,hct⟩ hc.2 hlast hψ.continuous heq'
  exact ⟨c,hc,d',L,ψ,hS,hd',hpass',hcap,hlast,hψ,hm,heq,
    (fun r hr => ⟨hpos r hr,(hbounds r hr).2⟩),hprimitive⟩

end OptimalG.Variational
