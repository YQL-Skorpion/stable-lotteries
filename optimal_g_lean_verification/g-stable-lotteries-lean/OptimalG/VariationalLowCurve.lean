import OptimalG.VariationalContactContinuity
import OptimalG.VariationalContactDeficit
import OptimalG.VariationalSlopeIntegration
import Mathlib.Topology.Piecewise

/-! The concrete low-rank curve joins the cap derivative to the recovered
minimizing score. Numerical shape inputs remain explicit in the theorems. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology

noncomputable def capRegularScore (lam S c : ℝ) (psi : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ c then capScore lam S r else psi r

 theorem capRegularScore_left (lam S c : ℝ) (psi : ℝ → ℝ) {r : ℝ} (hr : r ≤ c) :
    capRegularScore lam S c psi r=capScore lam S r := if_pos hr

 theorem capRegularScore_right {lam S c r : ℝ} {psi : ℝ → ℝ}
    (hjoin : psi c=capScore lam S c) (hr : c ≤ r) : capRegularScore lam S c psi r=psi r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [capRegularScore,hjoin]
  · exact if_neg (not_le.mpr hr)

 theorem capRegularScore_continuousOn {lam S c a b : ℝ} {psi : ℝ → ℝ}
    (hb : b < 1) (hpsi : Continuous psi) (hjoin : psi c=capScore lam S c) :
    ContinuousOn (capRegularScore lam S c psi) (Icc a b) := by
  have hcap : ContinuousOn (capScore lam S) (Icc a b) := by
    intro r hr
    exact (capScore_hasDerivAt lam S r (ne_of_lt (hr.2.trans_lt hb))).continuousAt.continuousWithinAt
  apply ContinuousOn.if
  · intro r hr
    have he : r=c := by
      have hh := hr.2
      change r ∈ frontier (Iic c) at hh
      simpa only [frontier_Iic,mem_singleton_iff] using hh
    simpa [he] using hjoin.symm
  · exact hcap.mono inter_subset_left
  · exact hpsi.continuousOn

 theorem capScore_strictAntiOn {lam S a b : ℝ}
    (hlam : 0 < lam) (hS : 0 < S) (hb : b < 1) :
    StrictAntiOn (capScore lam S) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun r hr => (capScore_hasDerivAt lam S r (ne_of_lt (hr.2.trans_lt hb))).continuousAt.continuousWithinAt)
  intro r hr
  have hr' : r ∈ Icc a b := interior_subset hr
  rw [(capScore_hasDerivAt lam S r (ne_of_lt (hr'.2.trans_lt hb))).deriv]
  have hp : 0 < 2*lam*S := by positivity
  exact div_neg_of_neg_of_pos (by nlinarith only [hp]) (pow_pos (by linarith [hr'.2]) _)

 theorem capRegularScore_strictAntiOn {lam S c a b : ℝ} {psi : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hb : b < 1) (hlam : 0 < lam) (hS : 0 < S)
    (hjoin : psi c=capScore lam S c) (hpsi : StrictAntiOn psi (Icc c b)) :
    StrictAntiOn (capRegularScore lam S c psi) (Icc a b) := by
  have hcap := capScore_strictAntiOn (a:=a) (b:=c) hlam hS (hcb.trans_lt hb)
  intro r hr s hs hrs
  by_cases hsc : s ≤ c
  · rw [capRegularScore_left _ _ _ _ hsc,capRegularScore_left _ _ _ _ (hrs.le.trans hsc)]
    exact hcap ⟨hr.1,hrs.le.trans hsc⟩ ⟨hs.1,hsc⟩ hrs
  · have hcs : c < s := lt_of_not_ge hsc
    rw [capRegularScore_right hjoin hcs.le]
    by_cases hrc : r ≤ c
    · rw [capRegularScore_left _ _ _ _ hrc]
      have hh := hpsi ⟨le_rfl,hcb⟩ ⟨hcs.le,hs.2⟩ hcs
      rw [hjoin] at hh
      exact hh.trans_le (hcap.antitoneOn ⟨hr.1,hrc⟩ ⟨hac,le_rfl⟩ hrc)
    · rw [capRegularScore_right hjoin (le_of_not_ge hrc)]
      exact hpsi ⟨le_of_not_ge hrc,hr.2⟩ ⟨hcs.le,hs.2⟩ hrs

 theorem capRegularScore_lower_increment {lam S c a b : ℝ} {psi : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hb : b < 1)
    (hjoin : psi c=capScore lam S c)
    (hcurv : ∀ r ∈ Icc a c, -1 ≤ -2*lam*S/(1-r)^3)
    (hpsi : ∀ r ∈ Icc c b, ∀ s ∈ Icc c b, r ≤ s → psi r-(s-r) ≤ psi s) :
    ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s →
      capRegularScore lam S c psi r-(s-r) ≤ capRegularScore lam S c psi s := by
  have hcap : ∀ r ∈ Icc a c, ∀ s ∈ Icc a c, r ≤ s →
      capScore lam S r-(s-r) ≤ capScore lam S s := by
    intro r hr s hs hrs
    have hh := reference_primitive_lower_increment (a:=a) (b:=c) (m0:=-1)
      (fun t ht => capScore_hasDerivAt lam S t (ne_of_lt (ht.2.trans_lt (hcb.trans_lt hb))))
      (fun t ht => hcurv t ⟨ht.1.le,ht.2.le⟩) r hr s hs hrs
    linarith
  intro r hr s hs hrs
  by_cases hsc : s ≤ c
  · rw [capRegularScore_left _ _ _ _ hsc,capRegularScore_left _ _ _ _ (hrs.trans hsc)]
    exact hcap r ⟨hr.1,hrs.trans hsc⟩ s ⟨hs.1,hsc⟩ hrs
  · have hcs := (lt_of_not_ge hsc).le
    rw [capRegularScore_right hjoin hcs]
    by_cases hrc : r ≤ c
    · rw [capRegularScore_left _ _ _ _ hrc]
      have h1 := hcap r ⟨hr.1,hrc⟩ c ⟨hac,le_rfl⟩ hrc
      have h2 := hpsi c ⟨le_rfl,hcb⟩ s ⟨hcs,hs.2⟩ hcs
      rw [hjoin] at h2
      linarith
    · rw [capRegularScore_right hjoin (le_of_not_ge hrc)]
      exact hpsi r ⟨le_of_not_ge hrc,hr.2⟩ s ⟨hcs,hs.2⟩ hrs


 theorem capRegularScore_integral {lam S c a b : ℝ} {psi : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hb : b < 1)
    (hpsi : Continuous psi) (hjoin : psi c=capScore lam S c) :
    ∀ r ∈ Icc a b, cap lam S a+(∫ t in a..r,capRegularScore lam S c psi t) =
      if r ≤ c then cap lam S r else cap lam S c+∫ t in c..r,psi t := by
  have hscore := capRegularScore_continuousOn (a:=a) hb hpsi hjoin
  have hi {r s : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) :
      IntervalIntegrable (capRegularScore lam S c psi) volume r s :=
    (hscore.mono (uIcc_subset_Icc hr hs)).intervalIntegrable
  have hcapint {r : ℝ} (hr : r ∈ Icc a c) :
      (∫ t in a..r,capRegularScore lam S c psi t)=cap lam S r-cap lam S a := by
    have hi' : IntervalIntegrable (capScore lam S) volume a r := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hr.1] at ht
      exact (capScore_hasDerivAt lam S t
        (ne_of_lt ((ht.2.trans hr.2).trans_lt (hcb.trans_lt hb)))).continuousAt.continuousWithinAt
    calc
      _ = ∫ t in a..r,capScore lam S t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hr.1] at ht
        exact capRegularScore_left _ _ _ _ (ht.2.trans hr.2)
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
        cap_hasDerivAt lam S t (ne_of_lt (by
          rw [uIcc_of_le hr.1] at ht
          exact ((ht.2.trans hr.2).trans hcb).trans_lt hb))) hi'
  intro r hr
  by_cases hrc : r ≤ c
  · rw [if_pos hrc,hcapint ⟨hr.1,hrc⟩]
    ring
  · have hcr : c ≤ r := le_of_not_ge hrc
    rw [if_neg hrc,← intervalIntegral.integral_add_adjacent_intervals
      (hi ⟨le_rfl,hac.trans hcb⟩ ⟨hac,hcb⟩) (hi ⟨hac,hcb⟩ hr),hcapint ⟨hac,le_rfl⟩]
    have he : (∫ t in c..r,capRegularScore lam S c psi t)=∫ t in c..r,psi t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hcr] at ht
      exact capRegularScore_right hjoin ht.1
    rw [he]
    ring


 theorem capRegularScore_primitive {lam c a : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hac : a ≤ c) (hc : c ∈ Icc ell xHi)
    (hpsi : Continuous psi) (hjoin : psi c=capScore lam d.S c)
    (hcap : ∀ r ∈ Icc ell c, lowPrimitive lam d r=cap lam d.S r)
    (hprimitive : ∀ r ∈ Icc c xHi, lowPrimitive lam d r=cap lam d.S c+∫ t in c..r,psi t) :
    ∀ r ∈ Icc a xHi, primitive lam d r=cap lam d.S a+∫ t in a..r,capRegularScore lam d.S c psi t := by
  intro r hr
  rw [capRegularScore_integral hac hc.2 (by norm_num [xHi]) hpsi hjoin r hr]
  by_cases hrc : r ≤ c
  · rw [if_pos hrc]
    by_cases hre : r ≤ ell
    · simp only [primitive,if_pos hre]
    · rw [primitive,if_neg hre,if_pos (hr.2.trans (by norm_num [xHi,tEnd]))]
      exact hcap r ⟨le_of_not_ge hre,hrc⟩
  · rw [if_neg hrc,primitive,if_neg (not_le.mpr (hc.1.trans_lt (lt_of_not_ge hrc))),
      if_pos (hr.2.trans (by norm_num [xHi,tEnd]))]
    exact hprimitive r ⟨le_of_not_ge hrc,hr.2⟩

 theorem antitone_lower_increment_lipschitz {a b : ℝ} {f : ℝ → ℝ}
    (hm : AntitoneOn f (Icc a b))
    (hl : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, r ≤ s → f r-(s-r) ≤ f s) :
    LipschitzOnWith 1 f (Icc a b) := by
  have hdist {r s : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) (hrs : r ≤ s) :
      dist (f r) (f s) ≤ dist r s := by
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hm hr hs hrs)),
      abs_of_nonpos (sub_nonpos.mpr hrs)]
    linarith [hl r hr s hs hrs]
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  simp only [NNReal.coe_one,one_mul]
  rcases le_total r s with hrs | hsr
  · exact hdist hr hs hrs
  · simpa only [dist_comm] using hdist hs hr hsr

 theorem derivative_lower_of_increment {a b r : ℝ} {f : ℝ → ℝ}
    (hl : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v → f u-(v-u) ≤ f v)
    (hr : r ∈ Ioo a b) : -1 ≤ deriv f r := by
  by_cases hd : DifferentiableAt ℝ f r
  · have hm : MonotoneOn (fun t => f t+t) (Icc a b) := by
      intro u hu v hv huv
      linarith [hl u hu v hv huv]
    have hh := hm.derivWithin_nonneg (x:=r)
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)] at hh
    have hdadd := hd.hasDerivAt.add (hasDerivAt_id r)
    change HasDerivAt (fun t => f t+t) (deriv f r+1) r at hdadd
    rw [hdadd.deriv] at hh
    linarith
  · rw [deriv_zero_of_not_differentiableAt hd]
    norm_num


 theorem Admissible.capScore_bounds_left {lam c : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd)
    (hcontact : lowPrimitive lam d c=cap lam d.S c) :
    ∀ r ≤ c, 0 < capScore lam d.S r ∧ capScore lam d.S r ≤ lam-r := by
  have hL : 0 < lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hS : 0 < d.S := by linarith [hd.slack_lower]
  intro r hrc
  by_cases hre : ell ≤ r
  · exact hd.capScore_bounds_before_contact hc hcontact r ⟨hre,hrc⟩
  · have hrell : r ≤ ell := le_of_not_ge hre
    have hcap := (capScore_strictAntiOn (a:=r) (b:=ell) hL hS (by norm_num [ell])).antitoneOn
      (show r ∈ Icc r ell from ⟨le_rfl,hrell⟩) ⟨hrell,le_rfl⟩ hrell
    have hpositive := hd.capScore_pos (r:=ell) (by norm_num [ell,tEnd])
    refine ⟨hpositive.trans_le hcap,?_⟩
    have hquot : 0 ≤ lam*d.S/(1-r)^2 := div_nonneg (mul_nonneg hL.le hS.le) (sq_nonneg _)
    have hLlo := hd.1.1
    norm_num [lambdaLo,ell] at hLlo hrell
    unfold capScore
    linarith

 theorem capRegularScore_bounds {lam c a b : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hc : c ∈ Ioc ell tEnd)
    (hcontact : lowPrimitive lam d c=cap lam d.S c)
    (hpsi : ∀ r ∈ Icc c b, 0 < psi r ∧ psi r ≤ lam-r) :
    ∀ r ∈ Icc a b, 0 < capRegularScore lam d.S c psi r ∧
      capRegularScore lam d.S c psi r ≤ lam-r := by
  intro r hr
  by_cases hrc : r ≤ c
  · rw [capRegularScore_left _ _ _ _ hrc]
    exact hd.capScore_bounds_left hc hcontact r hrc
  · simp only [capRegularScore,if_neg hrc]
    exact hpsi r ⟨le_of_not_ge hrc,hr.2⟩

 theorem capRegularScore_line {lam S c a b : ℝ} {psi : ℝ → ℝ}
    (hca : c ≤ a) (hjoin : psi c=capScore lam S c)
    (hline : ∀ r ∈ Icc a b, psi r=lam-r) :
    ∀ r ∈ Icc a b, capRegularScore lam S c psi r=lam-r := by
  intro r hr
  rw [capRegularScore_right hjoin (hca.trans hr.1),hline r hr]


 theorem capRegularScore_continuous {lam S c : ℝ} {psi : ℝ → ℝ}
    (hc : c < 1) (hpsi : Continuous psi) (hjoin : psi c=capScore lam S c) :
    Continuous (capRegularScore lam S c psi) := by
  rw [← continuousOn_univ]
  apply ContinuousOn.if
  · intro r hr
    have he : r=c := by
      have hh := hr.2
      change r ∈ frontier (Iic c) at hh
      simpa only [frontier_Iic,mem_singleton_iff] using hh
    simpa [he] using hjoin.symm
  · intro r hr
    have hrc : r ≤ c := by
      have hh := hr.2
      change r ∈ closure (Iic c) at hh
      rw [isClosed_Iic.closure_eq] at hh
      exact hh
    exact (capScore_hasDerivAt lam S r (ne_of_lt (hrc.trans_lt hc))).continuousAt.continuousWithinAt
  · exact hpsi.continuousOn

 theorem Admissible.capRegularScore_ae {lam c : ℝ} {d : LowRankData} {psi : ℝ → ℝ}
    (hd : Admissible lam d) (hc : c ∈ Icc xLo xHi)
    (hcap : ∀ r ∈ Icc ell c, lowPrimitive lam d r=cap lam d.S r)
    (heq : d.phi =ᵐ[volume.restrict (Icc c xHi)] psi) :
    d.phi =ᵐ[volume.restrict (Icc xLo xHi)] capRegularScore lam d.S c psi := by
  have hne : ∀ᵐ r ∂volume, r ≠ c := by simp [ae_iff]
  have hright : ∀ᵐ r ∂volume, r ∈ Icc c xHi → d.phi r=psi r :=
    (ae_restrict_iff' measurableSet_Icc).mp heq
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hne,
    ae_restrict_of_ae hright,ae_restrict_of_ae hd.lowPrimitive_hasDerivAt_ae]
    with r hr hrne hrr hdr
  by_cases hrc : r ≤ c
  · have hrc' : r < c := lt_of_le_of_ne hrc hrne
    have her : ell < r := (by norm_num [ell,xLo] : ell < xLo).trans_le hr.1
    have hri : r ∈ Icc ell tEnd := ⟨her.le,hr.2.trans (by norm_num [xHi,tEnd])⟩
    have hdcap : HasDerivAt (cap lam d.S) (d.phi r) r := by
      apply (hdr hri).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds her hrc'] with t ht
      exact (hcap t ⟨ht.1.le,ht.2.le⟩).symm
    rw [capRegularScore_left _ _ _ _ hrc]
    exact hdcap.unique (cap_hasDerivAt lam d.S r
      (ne_of_lt (hr.2.trans_lt (by norm_num [xHi]))))
  · simp only [capRegularScore,if_neg hrc]
    exact hrr ⟨le_of_not_ge hrc,hr.2⟩

end OptimalG.Variational
