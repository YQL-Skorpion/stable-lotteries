import OptimalG.Certificates.StaticIntermediateSelectedDataBatch00
import OptimalG.Certificates.StaticIntermediateSelectedData.CapZero
import OptimalG.Certificates.StaticIntermediateSelectedDataBatch02
import OptimalG.Certificates.StaticIntermediateSelectedDataBatch01
import OptimalG.IntermediateSelectedAssembly

namespace OptimalG.Certificates.StaticIntermediateSelectedLinks
open Set IntermediateSelectedExpressions

theorem signs {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (22493/40000:ℝ) (13/20))
    (hz : z∈Icc (391/500:ℝ) (7/8))
    (hD : Certificates.LineControl.denominator (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)≠0) (hN : Certificates.LineControl.slopeNumerator (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)≠0) :
    IntermediateSelectedSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p z (cubicControlDeficit (Certificates.LineControl.slope (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) (Certificates.LineControl.alpha (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) (Certificates.LineControl.crossing (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) z) := by
  have hh := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
    (by linarith only [hL.1] : 0≤(StaticLow.lam:ℝ))
  have hsig : 0<Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000) := by
    unfold Variational.capSlack Variational.capScore
    norm_num
    nlinarith only [hh,hL.1]
  constructor
  · have hh := StaticIntermediateSelectedData.DeficitCoefficient.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.CapZero.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.CapBoundary.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.HeadSquare.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.CapMaximum.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.FreeLeft.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.FreeKink.positive hp hz
    linarith only [hh]
  · have hh := StaticIntermediateSelectedData.FreeRight.positive hp hz
    linarith only [hh]

end OptimalG.Certificates.StaticIntermediateSelectedLinks
