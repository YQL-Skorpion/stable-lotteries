import OptimalG.VariationalRankMatching
import OptimalG.VariationalWeakStar

/-! The change-of-variables derivative identity (B.8), including pullback of
all exceptional null sets by a possibly discontinuous monotone rank map. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal Topology

 theorem matched_rank_derivative {a b : ℝ} {K : ℝ≥0} {J Xi gamma phi m : ℝ → ℝ}
    (hg : MonotoneOn gamma (Icc a b))
    (hinj : InjOn gamma (Icc a b))
    (hinverse : ∀ r ∈ Icc a b, ∀ s ∈ Icc a b, dist r s ≤ K*dist (gamma r) (gamma s))
    (hmatch : ∀ r ∈ Icc a b, gamma r ∈ Icc a b ∧ J (gamma r) = Xi r)
    (hJ : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt J (phi s) s ∧ 0 ≤ phi s)
    (hXi : ∀ r ∈ Ioo a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, 0 < m r) :
    ∀ᵐ r ∂volume.restrict (Ioo a b),
      HasDerivAt gamma (deriv gamma r) r ∧ 0 < deriv gamma r ∧ phi (gamma r) = m r/deriv gamma r := by
  have hpull := ae_pullback_of_inverse_lipschitz measurableSet_Icc hinj hinverse hJ
  have hdiff := hg.ae_differentiableWithinAt measurableSet_Icc
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hpull,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hdiff] with r hr hJr hgr
  have hrcc : r ∈ Icc a b := ⟨hr.1.le,hr.2.le⟩
  have hga : DifferentiableAt ℝ gamma r := hgr.differentiableAt (Icc_mem_nhds hr.1 hr.2)
  have hj := hJr (hmatch r hrcc).1
  have hcomp := hj.1.comp r hga.hasDerivAt
  have hXi' : HasDerivAt Xi (phi (gamma r)*deriv gamma r) r := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    exact (hmatch s ⟨hs.1.le,hs.2.le⟩).2.symm
  have he := hXi'.unique (hXi r hr)
  have hprod : 0 < phi (gamma r)*deriv gamma r := by rw [he]; exact hm r hr
  have hdpos : 0 < deriv gamma r := pos_of_mul_pos_right hprod hj.2
  refine ⟨hga.hasDerivAt,hdpos,?_⟩
  exact (eq_div_iff hdpos.ne').2 he

 theorem Admissible.lowPrimitive_hasDerivAt_ae {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    ∀ᵐ r ∂volume, r ∈ Icc ell tEnd → HasDerivAt (lowPrimitive lam d) (d.phi r) r := by
  have hle : ell ≤ tEnd := by norm_num [ell,tEnd]
  have hi := (hd.intervalIntegrable le_rfl hle le_rfl).ae_hasDerivAt_integral
  filter_upwards [hi] with r hr hri
  exact (hr (by simpa only [uIcc_of_le hle] using hri)
    ell (by simp [uIcc_of_le hle,hle])).const_add (cap lam d.S ell)

end OptimalG.Variational
