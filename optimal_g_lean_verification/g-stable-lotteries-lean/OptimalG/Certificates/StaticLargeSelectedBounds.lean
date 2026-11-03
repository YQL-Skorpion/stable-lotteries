import OptimalG.Certificates.StaticLargeSelectedDataBatch01
import OptimalG.Certificates.StaticLargeSelectedDataBatch00
import OptimalG.Certificates.StaticLargeSelectedData.FreeKink
import OptimalG.LargeSelectedAssembly
import OptimalG.Certificates.LineControlBounds

namespace OptimalG.Certificates
open Set Variational LargeSelectedExpressions

theorem staticLargeSelected_signs 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) :
    LargeSelectedSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
  have hD := (LineControl.denominator_pos hL hS).ne'
  have hN := (LineControl.slopeNumerator_pos hL hS).ne'
  have hsig : capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000)≠0 := by
    apply ne_of_gt
    have hh := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
      (by linarith only [hL.1] : 0≤(StaticLow.lam:ℝ))
    norm_num [capSlack,capScore]
    nlinarith only [hh,hL.1]
  have hbase : (13/20:ℝ)∈Icc (13/20) (7/8) := ⟨le_rfl,by norm_num⟩
  constructor
  · constructor
    · intro p hp
      have hh := StaticLargeSelectedData.HeadMassDerivative.positive hp
      linarith only [hh]
    · intro p hp
      have hh := StaticLargeSelectedData.MiddleMassDerivative.positive hp
      linarith only [hh]
    · intro p hp
      have hh := StaticLargeSelectedData.LateMassDerivative.positive hp
      linarith only [hh]
    · have hh := StaticLargeSelectedData.FlatMaximum.positive hbase
      change capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (313/1000)≤3/10000
      change 0<3/10000-capDeficit (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (313/1000) at hh
      linarith only [hh]
  · intro z hz
    constructor
    · exact (StaticLargeSelectedData.HeadHeadDerivative.positive hz).le
    · exact (StaticLargeSelectedData.HeadFlatDerivative.positive hz).le
    · have hh := StaticLargeSelectedData.CapMaximum.positive hz
      linarith only [hh]
    · have hh := StaticLargeSelectedData.FreeLeft.positive hz
      linarith only [hh]
    · have hh := StaticLargeSelectedData.FreeRight.positive hz
      linarith only [hh]
    · have hh := StaticLargeSelectedData.FreeKink.positive hz
      linarith only [hh]
  · have hh := StaticLargeSelectedData.CubicMaximum.positive hbase
    linarith only [hh]
  · intro z hz
    have hh := StaticLargeSelectedData.SmallSplitK.positive hz
    linarith only [hh]

end OptimalG.Certificates
