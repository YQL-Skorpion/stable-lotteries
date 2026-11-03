import OptimalG.Certificates.StaticBinaryInputs
import OptimalG.VariationalCapControl
import OptimalG.VariationalRepresentativeGraph

namespace OptimalG.Certificates.StaticBinaryInputs
open Set Variational

theorem fixed_cap_support :
    ((1459/5000:ℝ),capScore StaticLow.lam staticLowData.S (1459/5000))∈
      rankScoreSupport staticLowData.phi := by
  have hh := staticLow_admissible.continuous_rep_score_mem
    (a:=xLo) (b:=xHi) (by norm_num [xLo,xHi]) le_rfl le_rfl
    StaticLow.continuous_score (Filter.EventuallyEq.rfl)
    (r:=(1459/5000:ℝ)) (by norm_num [xLo,xHi])
  have hs := StaticLow.score_cap (r:=(1459/5000:ℝ))
    (by norm_num [StaticLow.leftContact,UpperProfileData.leftContact])
  rw [hs] at hh
  exact hh

theorem fixed_cap_primitive :
    Variational.primitive StaticLow.lam staticLowData (29/100)=
      Variational.cap StaticLow.lam staticLowData.S (29/100) := by
  unfold Variational.primitive
  rw [if_neg (by norm_num [ell]),if_pos (by norm_num [tEnd]),lowPrimitive_staticLow]
  have hh := StaticLow.primitive_cap (r:=(29/100:ℝ))
    (by norm_num [StaticLow.leftContact,UpperProfileData.leftContact])
  exact hh

theorem fixed_cap_control
    (hcontrols : ∀ z∈Icc zStart 1,∀v∈controlFeatureSupport staticLowData,
      StaticCurve.score z≤featureH staticLow_admissible z
        (curvePrimitive StaticCurve.score z) v) :
    ∀ z∈Ioo (807/1000:ℝ) StaticContact.entry,
      StaticCurve.score z≤highAffineControl StaticLow.lam StaticLow.slack (29/100)
        (capDiagonalTheta StaticLow.lam StaticLow.slack (29/100) (1459/5000))
        (capDiagonalAlpha StaticLow.lam StaticLow.slack (29/100) (1459/5000)) Y z := by
  have hv := staticLow_admissible.feature_mem_support_of_rankScores
    (p:=(29/100:ℝ)) (by norm_num [pLo,pHi]) fixed_cap_support fixed_cap_support (by norm_num)
  have hc := capDiagonal_coefficients (lam:=(StaticLow.lam:ℝ)) (d:=staticLowData)
    (p:=(29/100:ℝ)) (r:=(1459/5000:ℝ)) fixed_cap_primitive
  intro z hz
  have hz' : z∈Icc zStart 1 := by
    constructor
    · norm_num [zStart]
      linarith only [hz.1]
    · have hh := StaticContact.entry_mem.2
      linarith only [hz.2,hh]
  have hh := hcontrols z hz' _ hv
  have he : curvePrimitive StaticCurve.score z=Y z :=
    actual (hz.2.le.trans StaticContact.entry_le_contact)
  rw [he,featureH_as_highAffineControl staticLow_admissible hv Y z] at hh
  dsimp only [Prod.fst,Prod.snd] at hh
  rw [hc.1,hc.2] at hh
  exact hh

end OptimalG.Certificates.StaticBinaryInputs
