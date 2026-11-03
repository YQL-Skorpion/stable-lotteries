import OptimalG.SupportingMinimum
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Quantitative regularity of the supporting infimum on target intervals
strictly above λ. The lower score bound is derived from the actual minimizer,
so Lipschitz regularity does not assume a selection of minimizing ranks. -/
namespace OptimalG
open Set
open scoped NNReal

noncomputable def supportScoreFloor (phi : ℝ → ℝ) (lam lo hi : ℝ) : ℝ :=
  (lo-lam)*phi 0/hi

theorem supportScoreFloor_pos {phi : ℝ → ℝ} {lam lo hi : ℝ}
    (hlam : 0<lam) (hp0 : 0<phi 0) (hlo : lam<lo) (hhi : lo≤hi) :
    0<supportScoreFloor phi lam lo hi :=
  div_pos (mul_pos (sub_pos.mpr hlo) hp0) (hlam.trans (hlo.trans_le hhi))

/-- A minimizer cannot have arbitrarily small score when its target stays
strictly above λ: comparison with rank zero supplies a uniform positive floor. -/
theorem supportMinimum_score_lower {phi : ℝ → ℝ} {lam lo hi m x : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hlo : lam<lo) (hm : m ∈ Icc lo hi) (hx : x ∈ Ico 0 lam)
    (hmin : supportMinimum phi lam m=(m-x)/phi x) :
    supportScoreFloor phi lam lo hi≤phi x := by
  have hp0 := hp 0 ⟨le_rfl,hlam⟩
  have hpx := hp x hx
  have hmpos : 0<m := hlam.trans (hlo.trans_le hm.1)
  have hhipos := hmpos.trans_le hm.2
  have hh := supportMinimum_le_ratio hlam hc hz hp (hlo.trans_le hm.1)
    (show (0:ℝ) ∈ Ico 0 lam from ⟨le_rfl,hlam⟩)
  rw [hmin,sub_zero] at hh
  have hcross := (div_le_div_iff₀ hpx hp0).mp hh
  have hlow : lo-lam≤m-x := by linarith [hx.2.le,hm.1]
  have hL := mul_le_mul_of_nonneg_right hlow hp0.le
  have hU := mul_le_mul_of_nonneg_right hm.2 hpx.le
  apply (div_le_iff₀ hhipos).mpr
  change (lo-lam)*phi 0≤phi x*hi
  nlinarith

theorem supportMinimum_difference_le {phi : ℝ → ℝ} {lam lo hi a b : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hlo : lam<lo) (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) (hab : a≤b) :
    supportMinimum phi lam b-supportMinimum phi lam a≤
      (b-a)/supportScoreFloor phi lam lo hi := by
  obtain ⟨_,x,hx,hmin,_⟩ := supportMinimum_attained hlam hc hz hp (hlo.trans_le ha.1)
  have hh := supportMinimum_compare_at_minimizer hlam hc hz hp (hlo.trans_le hb.1) hx hmin
  have hxlow := supportMinimum_score_lower hlam hc hz hp hlo ha hx hmin
  have hk := supportScoreFloor_pos hlam (hp 0 ⟨le_rfl,hlam⟩) hlo (ha.1.trans ha.2)
  apply hh.trans
  apply (div_le_div_iff₀ (hp x hx) hk).mpr
  exact mul_le_mul_of_nonneg_left hxlow (sub_nonneg.mpr hab)

/-- The actual infimum is Lipschitz on every compact target interval above λ. -/
theorem supportMinimum_lipschitzOn {phi : ℝ → ℝ} {lam lo hi : ℝ}
    (hlam : 0<lam) (hc : ContinuousOn phi (Icc 0 lam))
    (hz : phi lam=0) (hp : ∀ x ∈ Ico 0 lam, 0<phi x)
    (hlo : lam<lo) (hhi : lo≤hi) :
    ∃ K : ℝ≥0, (K:ℝ)=1/supportScoreFloor phi lam lo hi ∧
      LipschitzOnWith K (supportMinimum phi lam) (Icc lo hi) := by
  have hk := supportScoreFloor_pos hlam (hp 0 ⟨le_rfl,hlam⟩) hlo hhi
  let K : ℝ≥0 := ⟨1/supportScoreFloor phi lam lo hi,(div_pos zero_lt_one hk).le⟩
  have hmono := (supportMinimum_strictMonoOn hlam hc hz hp).monotoneOn
  have hdist (a : ℝ) (ha : a ∈ Icc lo hi) (b : ℝ) (hb : b ∈ Icc lo hi) (hab : a≤b) :
      dist (supportMinimum phi lam a) (supportMinimum phi lam b)≤(K:ℝ)*dist a b := by
    have hη := hmono (hlo.trans_le ha.1) (hlo.trans_le hb.1) hab
    have hh := supportMinimum_difference_le hlam hc hz hp hlo ha hb hab
    rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hη),
      abs_of_nonpos (sub_nonpos.mpr hab),neg_sub,neg_sub]
    change _≤(1/supportScoreFloor phi lam lo hi)*(b-a)
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh
  refine ⟨K,rfl,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  rcases le_total a b with hab | hba
  · exact hdist a ha b hb hab
  · simpa only [dist_comm] using hdist b hb a ha hba

end OptimalG
