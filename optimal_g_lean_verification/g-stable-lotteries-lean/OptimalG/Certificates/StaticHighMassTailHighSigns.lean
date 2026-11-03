import OptimalG.Certificates.StaticHighMassTailLinkBatch06
import OptimalG.Certificates.StaticHighMassTailLinkBatch07
import OptimalG.Certificates.StaticHighMassTailLinkBatch08
import OptimalG.Certificates.StaticHighMassTailLinkBatch09
import OptimalG.Certificates.StaticHighMassTailLinkBatch10
import OptimalG.Certificates.StaticHighMassTailLinkBatch11
import OptimalG.LargeTailHighAssembly

namespace OptimalG.Certificates.StaticHighMassTailHighSigns
open Set LargeTailExpressions
theorem slack_pos 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) :
    0<Variational.capSlack (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (1459/5000) := by
  have hh := mul_le_mul hL.1 hS.1 (by norm_num : (0:ℝ)≤227179/10000000)
    (by linarith only [hL.1] : 0≤(StaticLow.lam:ℝ))
  norm_num [Variational.capSlack,Variational.capScore]
  nlinarith only [hh,hL.1]
theorem LineUpper0 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (13/20) (391/500)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.LineUpper0HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper0HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper0HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper0HighForwardKink.bound hL hS hp hz hs
theorem LineUpper1 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (13/20) (391/500)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.LineUpper1HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper1HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper1HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.LineUpper1HighForwardKink.bound hL hS hp hz hs
theorem CurvedLower0 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (391/500) (41/50)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower0HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower0HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower0HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower0HighForwardKink.bound hL hS hp hz hs
theorem CurvedLower1 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (391/500) (41/50)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower1HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower1HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower1HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedLower1HighForwardKink.bound hL hS hp hz hs
theorem CurvedUpper0 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (391/500) (41/50)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper0HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper0HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper0HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper0HighForwardKink.bound hL hS hp hz hs
theorem CurvedUpper1 {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (391/500) (41/50)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailHighSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  have hs := (slack_pos hL hS).ne'
  constructor
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper1HighCapMax.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardLeft.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardRight.bound hL hS hp hz hs
  · exact StaticHighMassTailLinks.FullHigh.CurvedUpper1HighForwardKink.bound hL hS hp hz hs
end OptimalG.Certificates.StaticHighMassTailHighSigns
