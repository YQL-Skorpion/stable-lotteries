import OptimalG.Certificates.StaticIntermediateTailDataBatch01
import OptimalG.Certificates.StaticIntermediateTailDataBatch02
import OptimalG.Certificates.StaticIntermediateTailDataBatch00
import OptimalG.IntermediateTailAssembly

namespace OptimalG.Certificates.StaticIntermediateTailLinks
open Set IntermediateTailExpressions

theorem lo {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (22493/40000:ℝ) (13/20)) :
    IntermediateTailPolynomialSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (-(3589/10000)) := by
  constructor
  · intro z hz
    constructor
    · have hh := StaticIntermediateTailData.HighHeadLo.numerator_pos (pad:=0) hp hz (by norm_num)
      rw [StaticIntermediateTailData.HighHeadLo.expression_identity] at hh
      linarith only [hh]
    · have hh := StaticIntermediateTailData.HighLambdaLo.numerator_pos (pad:=0) hp hz (by norm_num)
      rw [StaticIntermediateTailData.HighLambdaLo.expression_identity] at hh
      linarith only [hh]
  · intro z hz
    have hh := StaticIntermediateTailData.HeadSquareLo.numerator_pos (pad:=0) hp hz (by norm_num)
    rw [StaticIntermediateTailData.HeadSquareLo.expression_identity] at hh
    linarith only [hh]
  · intro u hu
    have hpu : u*(p-103/200)≤p-103/200 := by
      have hh := mul_le_mul_of_nonneg_right hu.2 (by linarith only [hp.1] : 0≤p-103/200)
      simpa only [one_mul] using hh
    constructor
    · apply capCore_nonpos_of_cleared (by linarith only [hpu])
      have hh := StaticIntermediateTailData.CapZeroLo.numerator_pos (pad:=0) hp hu (by norm_num)
      rw [StaticIntermediateTailData.CapZeroLo.expression_identity] at hh
      linarith only [hh]
    · apply capCore_nonpos_of_cleared (by linarith only [hpu])
      have hh := StaticIntermediateTailData.CapBoundaryLo.numerator_pos (pad:=0) hp hu (by norm_num)
      rw [StaticIntermediateTailData.CapBoundaryLo.expression_identity] at hh
      linarith only [hh]

theorem hi {p : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (22493/40000:ℝ) (13/20)) :
    IntermediateTailPolynomialSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (-(1757/5000)) := by
  constructor
  · intro z hz
    constructor
    · have hh := StaticIntermediateTailData.HighHeadHi.numerator_pos (pad:=0) hp hz (by norm_num)
      rw [StaticIntermediateTailData.HighHeadHi.expression_identity] at hh
      linarith only [hh]
    · have hh := StaticIntermediateTailData.HighLambdaHi.numerator_pos (pad:=0) hp hz (by norm_num)
      rw [StaticIntermediateTailData.HighLambdaHi.expression_identity] at hh
      linarith only [hh]
  · intro z hz
    have hh := StaticIntermediateTailData.HeadSquareHi.numerator_pos (pad:=0) hp hz (by norm_num)
    rw [StaticIntermediateTailData.HeadSquareHi.expression_identity] at hh
    linarith only [hh]
  · intro u hu
    have hpu : u*(p-103/200)≤p-103/200 := by
      have hh := mul_le_mul_of_nonneg_right hu.2 (by linarith only [hp.1] : 0≤p-103/200)
      simpa only [one_mul] using hh
    constructor
    · apply capCore_nonpos_of_cleared (by linarith only [hpu])
      have hh := StaticIntermediateTailData.CapZeroHi.numerator_pos (pad:=0) hp hu (by norm_num)
      rw [StaticIntermediateTailData.CapZeroHi.expression_identity] at hh
      linarith only [hh]
    · apply capCore_nonpos_of_cleared (by linarith only [hpu])
      have hh := StaticIntermediateTailData.CapBoundaryHi.numerator_pos (pad:=0) hp hu (by norm_num)
      rw [StaticIntermediateTailData.CapBoundaryHi.expression_identity] at hh
      linarith only [hh]

end OptimalG.Certificates.StaticIntermediateTailLinks
