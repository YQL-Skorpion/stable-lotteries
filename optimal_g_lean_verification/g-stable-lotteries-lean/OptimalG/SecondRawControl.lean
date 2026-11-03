import OptimalG.RelocationBinary
import OptimalG.RawControlSupport

/-! The final concrete relocated primitive has a uniform positive determinant
and a well-posed signed control field, before any running-envelope replacement. -/
namespace OptimalG.Relocation
open Set Variational
open scoped NNReal

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

theorem second_raw_determinant (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) (c : Control) (hc : c ∈ controlDomain) :
    (0.0519 : ℝ) ≤ rawDet lam (secondExtendedPrimitive lam phi) c := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    convert! hc.1 using 1 <;> norm_num [pLo,pHi]
  have hx : c.2.1 ∈ Icc (0.285 : ℝ) 0.38 := by
    convert! hc.2.1 using 1 <;> norm_num [xLo,xHi]
  have hy : c.2.2 ∈ Icc (0.285 : ℝ) 0.38 := by
    have hh : c.2.2 ∈ Icc xLo xHi := ⟨(le_max_left xLo c.1).trans hc.2.2.1,hc.2.2.2⟩
    convert! hh using 1 <;> norm_num [xLo,xHi]
  obtain ⟨hm1,hm2,hmt⟩ := mass_budget h hL hLP
  have heta : prefixGain lam phi ∈ Icc (0 : ℝ) (2.98*0.00025509854) := by
    unfold prefixGain
    constructor
    · exact mul_nonneg (by norm_num) hm1
    · exact mul_le_mul_of_nonneg_left (by linarith : massOne lam phi ≤ 0.00025509854) (by norm_num)
  let delta := slack lam phi (1-c.1)-slack lam phi 0.38
  have hd0 := slack_monotone h (show (0.38 : ℝ) ≤ 1-c.1 by linarith [hp.2])
  have hdhi := slack_monotone h (show 1-c.1 ≤ (0.775 : ℝ) by linarith [hp.1])
  have hdelta : delta ∈ Icc (0 : ℝ) 0.00025509854 := by
    unfold massOne massTwo at hmt
    dsimp [delta]
    constructor <;> linarith
  have hR : secondExtendedPrimitive lam phi c.1 = activationPrimitive phi c.1+prefixGain lam phi := by
    rw [secondExtendedPrimitive,second_low_eq h hL hLP (by linarith [hp.2]),
      first_low_eq h hL hLP ⟨by linarith [hp.1],by linarith [hp.2]⟩,
      extendedPrimitive_eq phi ⟨by linarith [hp.1],by linarith [hp.2]⟩]
    ring
  have hP : secondExtendedPrimitive lam phi (1-c.1) =
      activationPrimitive phi (1-c.1)+prefixGain lam phi+delta := by
    have hr : 1-c.1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith [hp.1]⟩
    rw [secondExtended_eq lam phi hr,secondPrimitive_middle h hL hLP
      ⟨by linarith [hp.2],by linarith [hp.1]⟩]
    have he := slack_eq lam phi hr
    unfold cumulativeSlack at he
    dsimp [delta]
    linarith
  have hb := h.bounded_slack_phase_boxes hL hLP hp hx hy heta hdelta
  unfold rawDet
  rw [hR,hP]
  exact hb.2.2.1.le

theorem second_raw_regular (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) :
    ∃ K : ℝ≥0, (∀ z, LipschitzWith K (rawVectorField lam (secondExtendedPrimitive lam phi) phi z)) ∧
      ∀ u, Continuous (fun z => rawVectorField lam (secondExtendedPrimitive lam phi) phi z u) := by
  obtain ⟨K,hK⟩ := secondExtended_lipschitz h
  have hphi : ContinuousOn phi (Icc xLo xHi) :=
    h.continuous.mono (Icc_subset_Icc (by norm_num [xLo]) (by norm_num [xHi]))
  have hs := raw_scores_bounded hphi
  exact rawVectorField_regular hK (by norm_num : (0 : ℝ) < 0.0519)
    (second_raw_determinant h hL hLP) hs.1 hs.2

end OptimalG.Relocation
