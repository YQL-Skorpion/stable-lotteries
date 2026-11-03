import OptimalG.RationalStationaryCurve
import OptimalG.BarrierComparisonAE
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual implicit branch supplies the regularity needed by the AE
barrier comparison: both the barrier and its first derivative are Lipschitz
on the compact branch rectangle. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

private noncomputable def stationaryArguments (lam S : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (v.1*((1-v.1)-capSlack lam S v.2),
    1-2*v.1-capSlack lam S v.2+v.1*(1-v.1)/(lam-v.2))

private theorem stationaryArguments_contDiffAt {lam S : ℝ} {v : ℝ × ℝ}
    (h1 : v.2≠1) (hlam : v.2≠lam) : ContDiffAt ℝ 1 (stationaryArguments lam S) v := by
  have hpow : (1-v.2)^2≠0 := pow_ne_zero 2 (sub_ne_zero.mpr h1.symm)
  have hden : lam-v.2≠0 := sub_ne_zero.mpr hlam.symm
  have hs : ContDiffAt ℝ 1 (fun v : ℝ × ℝ => capSlack lam S v.2) v := by
    unfold capSlack capScore
    exact (contDiffAt_const.sub contDiffAt_snd).sub
      (contDiffAt_const.sub (contDiffAt_const.div
        ((contDiffAt_const.sub contDiffAt_snd).pow 2) hpow))
  unfold stationaryArguments
  apply ContDiffAt.prodMk
  · exact contDiffAt_fst.mul ((contDiffAt_const.sub contDiffAt_fst).sub hs)
  · exact ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_fst)).sub hs).add
      ((contDiffAt_fst.mul (contDiffAt_const.sub contDiffAt_fst)).div
        (contDiffAt_const.sub contDiffAt_snd) hden)

theorem stationaryBarrier_lipschitz {lam S a b u v : ℝ} {q : ℝ → ℝ} {K : ℝ≥0}
    (hqlip : LipschitzOnWith K q (Icc a b))
    (hq : ∀ p ∈ Icc a b,q p ∈ Icc u v) (hv1 : v<1) (hvl : v<lam) :
    ∃ L : ℝ≥0,LipschitzOnWith L (stationaryBarrier lam S q) (Icc a b) ∧
      LipschitzOnWith L (stationaryBarrierSlope lam S q) (Icc a b) := by
  let C : Set (ℝ × ℝ) := Icc a b ×ˢ Icc u v
  have hC : IsCompact C := isCompact_Icc.prod isCompact_Icc
  have hlocal : LocallyLipschitzOn C (stationaryArguments lam S) := by
    intro w hw
    have hw1 : w.2≠1 := ne_of_lt (hw.2.2.trans_lt hv1)
    have hwl : w.2≠lam := ne_of_lt (hw.2.2.trans_lt hvl)
    obtain ⟨L,U,hU,hL⟩ := (stationaryArguments_contDiffAt (S:=S) hw1 hwl).exists_lipschitzOnWith
    exact ⟨L,U,mem_nhdsWithin_of_mem_nhds hU,hL⟩
  obtain ⟨L,hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hC hlocal
  have hpair := hL.comp ((LipschitzWith.id.lipschitzOnWith).prodMk hqlip)
    (show MapsTo (fun p => (p,q p)) (Icc a b) C from fun p hp => ⟨hp,hq p hp⟩)
  refine ⟨L*max 1 K,?_,?_⟩
  · convert! LipschitzWith.prod_fst.comp_lipschitzOnWith hpair using 1 <;>
      first | rfl | simp only [one_mul,Function.comp_def,stationaryArguments,stationaryBarrier,id_eq]
  · convert! LipschitzWith.prod_snd.comp_lipschitzOnWith hpair using 1 <;>
      first | rfl | simp only [one_mul,Function.comp_def,stationaryArguments,stationaryBarrierSlope,id_eq]

theorem stationaryBarrier_absolutelyContinuous {lam S a b u v : ℝ} {q : ℝ → ℝ} {K : ℝ≥0}
    (hab : a≤b) (hqlip : LipschitzOnWith K q (Icc a b))
    (hq : ∀ p ∈ Icc a b,q p ∈ Icc u v) (hv1 : v<1) (hvl : v<lam) :
    AbsolutelyContinuousOnInterval (stationaryBarrier lam S q) a b ∧
      AbsolutelyContinuousOnInterval (stationaryBarrierSlope lam S q) a b := by
  obtain ⟨L,hL,hL'⟩  := stationaryBarrier_lipschitz (S:=S) hqlip hq hv1 hvl
  constructor
  · apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hL
  · apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hL'

/-- Actual rational-branch comparison against a concave high score. The
barrier derivatives and AC properties are derived from the matching branch;
only the AE numerical curvature comparison and endpoint data remain inputs. -/
theorem rational_stationary_barrier_comparison {lam S a b u v : ℝ}
    {q Y phi : ℝ → ℝ} {K : ℝ≥0}
    (hab : a≤b) (hla : lam<a) (hb1 : b<1)
    (hqlip : LipschitzOnWith K q (Icc a b))
    (hq : ∀ p ∈ Icc a b,q p ∈ Icc u v) (hv1 : v<1) (hvl : v<lam)
    (hgap : ∀ r ∈ Icc u v,0<capSlopeGap lam S r)
    (hmatch : ∀ p ∈ Icc a b,stationaryLevel lam S (q p)=(1-p)^2)
    (hY : ContinuousOn Y (Icc a b)) (hphi : ConcaveOn ℝ (Icc lam 1) phi)
    (hYd : ∀ p ∈ Ioo a b,HasDerivAt Y (phi p) p)
    (hcurvature : ∀ᵐ p ∂volume.restrict (Icc a b),
      stationaryBarrierCurvature lam S p (q p)≤deriv phi p)
    (hvalue : stationaryBarrier lam S q a≤Y a)
    (hslope : stationaryBarrierSlope lam S q a≤phi a) :
    ∀ p ∈ Icc a b,stationaryBarrier lam S q p≤Y p := by
  obtain ⟨L,hTlip,_⟩  := stationaryBarrier_lipschitz (S:=S) hqlip hq hv1 hvl
  have hdTac := (stationaryBarrier_absolutelyContinuous (S:=S) hab hqlip hq hv1 hvl).2
  have hphiac := concave_absolutelyContinuousOnInterval hphi hab hla hb1
  have hqd (p : ℝ) (hp : p ∈ Ioo a b) :
      HasDerivAt q ((1-p)/((lam-q p)*capSlopeGap lam S (q p))) p :=
    stationary_branch_hasDerivAt hp hqlip.continuousOn hmatch
      ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hvl)
      (ne_of_lt ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hv1))
      (hgap (q p) (hq p ⟨hp.1.le,hp.2.le⟩))
  have hTd (p : ℝ) (hp : p ∈ Ioo a b) :
      HasDerivAt (stationaryBarrier lam S q) (stationaryBarrierSlope lam S q p) p :=
    stationaryBarrier_hasDerivAt (hqd p hp)
      (ne_of_lt ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hvl))
      (ne_of_lt ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hv1))
      (hgap (q p) (hq p ⟨hp.1.le,hp.2.le⟩)).ne'
  have hdTd (p : ℝ) (hp : p ∈ Ioo a b) :
      HasDerivAt (stationaryBarrierSlope lam S q) (stationaryBarrierCurvature lam S p (q p)) p :=
    stationaryBarrierSlope_hasDerivAt (hqd p hp)
      (ne_of_lt ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hvl))
      (ne_of_lt ((hq p ⟨hp.1.le,hp.2.le⟩).2.trans_lt hv1))
      (hgap (q p) (hq p ⟨hp.1.le,hp.2.le⟩)).ne'
  apply barrier_comparison_of_ac_slopes hY hTlip.continuousOn hphiac hdTac hYd hTd
    ?_ hvalue hslope
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hcurvature] with p hp hpc
  rw [(hdTd p hp).deriv]
  exact hpc

end OptimalG.Variational
