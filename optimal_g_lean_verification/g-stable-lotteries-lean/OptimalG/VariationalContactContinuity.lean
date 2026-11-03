import OptimalG.VariationalNormalizedMinimizer
import OptimalG.VariationalMatchedDerivative
import OptimalG.VariationalIntervalSupport

/-! Once the last contact lies strictly inside the tested rank interval,
cap normalization and the actual active-control bounds force a continuous
join of the score to the cap derivative. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

 theorem Admissible.capScore_mem_support_at_contact {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioo xLo xHi)
    (hcap : ∀ r ∈ Icc ell c, lowPrimitive lam d r = cap lam d.S r) :
    (c,capScore lam d.S c) ∈ rankScoreSupport d.phi := by
  have hce : ell < c := (by norm_num [ell,xLo] : ell < xLo).trans hc.1
  have hc1 : c < 1 := hc.2.trans (by norm_num [xHi])
  let clamp := fun r : ℝ => max xLo (min c r)
  have hclamp : Continuous clamp := continuous_const.max (continuous_const.min continuous_id)
  have hclamp_le (r : ℝ) : clamp r ≤ c := max_le hc.1.le (min_le_left _ _)
  let f := fun r => capScore lam d.S (clamp r)
  have hcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (capScore_hasDerivAt lam d.S (clamp r) (ne_of_lt ((hclamp_le r).trans_lt hc1))).continuousAt.comp
      hclamp.continuousAt
  have hAE : d.phi =ᵐ[volume.restrict (Ioo xLo c)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae hd.lowPrimitive_hasDerivAt_ae] with r hr hdr
    have hrFull : r ∈ Icc ell tEnd :=
      ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans hr.1.le,
        hr.2.le.trans (hc.2.le.trans (by norm_num [xHi,tEnd]))⟩
    have hdcap : HasDerivAt (cap lam d.S) (d.phi r) r := by
      apply (hdr hrFull).congr_of_eventuallyEq
      have her : ell < r := (by norm_num [ell,xLo] : ell < xLo).trans hr.1
      filter_upwards [Ioo_mem_nhds her hr.2] with t ht
      exact (hcap t ⟨ht.1.le,ht.2.le⟩).symm
    have he := hdcap.unique (cap_hasDerivAt lam d.S r (ne_of_lt (hr.2.trans hc1)))
    simpa only [f,clamp,min_eq_right hr.2.le,max_eq_right hr.1.le] using he
  have hg := hd.continuous_rep_score_mem hc.1 le_rfl hc.2.le hcont hAE (r:=c) ⟨hc.1.le,le_rfl⟩
  simpa only [f,clamp,min_self,max_eq_right hc.1.le] using hg

 theorem left_contact_derivative_nonneg {a b v : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hmin : IsMinOn f (Icc a b) a) (hd : HasDerivAt f v a) : 0 ≤ v := by
  have ht : b-a ∈ posTangentConeAt (Icc a b) a :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩)
  have hh := hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht
  change 0 ≤ (b-a)*v at hh
  nlinarith

 theorem representative_le_capScore_at_contact {lam c : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hc : c ∈ Ico xLo xHi) (hpsi : Continuous psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r,psi t) :
    psi c ≤ capScore lam d.S c := by
  let gap := fun r => cap lam d.S r-(cap lam d.S c+∫ t in c..r,psi t)
  have hmin : IsMinOn gap (Icc c xHi) c := by
    intro r hr
    have hcap := hd.lowPrimitive_le_cap
      (show r ∈ Icc ell tEnd from
        ⟨(by norm_num [ell,xLo] : ell ≤ xLo).trans (hc.1.trans hr.1),
          hr.2.trans (by norm_num [xHi,tEnd])⟩)
    rw [hprimitive r hr] at hcap
    change gap c ≤ gap r
    simp only [gap,intervalIntegral.integral_same,add_zero,sub_self]
    linarith
  have hderI := (intervalIntegral.integral_hasDerivAt_right (hpsi.intervalIntegrable c c)
    (hpsi.stronglyMeasurableAtFilter volume (𝓝 c)) hpsi.continuousAt).const_add (cap lam d.S c)
  have hder := (cap_hasDerivAt lam d.S c (ne_of_lt (hc.2.trans (by norm_num [xHi])))).sub hderI
  have h := left_contact_derivative_nonneg hc.2 hmin hder
  linarith

 theorem minimizer_score_continuous_at_contact {lam c : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hl : lambdaLo < lam)
    (hmin : ∀ lam', Feasible lam' → lam ≤ lam')
    (hpass : PassesTerminalTests lam d (continuation lam d))
    (hc : c ∈ Ioo xLo xHi)
    (hcap : ∀ r ∈ Icc ell c, lowPrimitive lam d r = cap lam d.S r)
    (hlast : ∀ r ∈ Icc ell tEnd, lowPrimitive lam d r = cap lam d.S r → r ≤ c)
    (hpsi : Continuous psi) (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r = cap lam d.S c+∫ t in c..r,psi t) :
    psi c = capScore lam d.S c := by
  have hce : ell ≤ c := (by norm_num [ell,xLo] : ell ≤ xLo).trans hc.1.le
  have hct : c ≤ tEnd := hc.2.le.trans (by norm_num [xHi,tEnd])
  obtain ⟨L,hL,hleft⟩ := minimizer_ae_left_bound hd hl hmin hpass ⟨hce,hct⟩ hlast
  have hgraph := hd.capScore_mem_support_at_contact hc hcap
  have hclosed : IsClosed {r : ℝ | capScore lam d.S c-psi r ≤ (L:ℝ)*(r-c)} :=
    isClosed_le (continuous_const.sub hpsi) (continuous_const.mul (continuous_id.sub continuous_const))
  have hsub : Ioo c xHi ⊆ Icc ell tEnd := by
    intro r hr
    exact ⟨hce.trans hr.1.le,hr.2.le.trans (by norm_num [xHi,tEnd])⟩
  have hae : ∀ᵐ r ∂volume.restrict (Ioo c xHi),
      r ∈ {r : ℝ | capScore lam d.S c-psi r ≤ (L:ℝ)*(r-c)} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset hsub hleft,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self heq] with r hr hlr heqr
    have hh := hlr hr.1 (c,capScore lam d.S c) hgraph hr.1.le
    simpa only [heqr] using hh
  have hcSupport := mem_support_open_interval_of_closed hc.2 (show c ∈ Icc c xHi from ⟨le_rfl,hc.2.le⟩)
  have hh := (volume.restrict (Ioo c xHi)).support_subset_of_isClosed hclosed hae hcSupport
  have hlow : capScore lam d.S c ≤ psi c := by
    change capScore lam d.S c-psi c ≤ (L:ℝ)*(c-c) at hh
    nlinarith only [hh]
  exact le_antisymm (representative_le_capScore_at_contact hd ⟨hc.1.le,hc.2⟩ hpsi hprimitive) hlow


 theorem right_contact_derivative_nonpos {f : ℝ → ℝ} {a b v : ℝ}
    (hab : a < b) (hmin : IsMinOn f (Icc a b) b) (hd : HasDerivAt f v b) : v ≤ 0 := by
  have ht : a-b ∈ posTangentConeAt (Icc a b) b :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨hab.le,le_rfl⟩ ⟨le_rfl,hab.le⟩)
  have hh := hmin.localize.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt ht
  change 0 ≤ (a-b)*v at hh
  nlinarith

end OptimalG.Variational
