import OptimalG.Certificates.StaticHighMassTailLinkBatch00
import OptimalG.Certificates.StaticHighMassTailLinkBatch01
import OptimalG.Certificates.StaticHighMassTailLinkBatch02
import OptimalG.Certificates.StaticHighMassTailLinkBatch03
import OptimalG.Certificates.StaticHighMassTailLinkBatch04
import OptimalG.Certificates.StaticHighMassTailLinkBatch05
import OptimalG.Certificates.StaticHighMassTailLinkBatch06
import OptimalG.LargeTailBeforeCoverage

namespace OptimalG.Certificates.StaticHighMassTailBeforeSigns
open Set LargeTailExpressions
theorem LineUpper0 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailLineRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-3589/10000) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper0HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper0CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper0HeadZeroTriangle.bound hL hS hp hu
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryTriangle.bound hL hS hp hu
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper0HeadZeroRectangle.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper0HeadCapBoundaryRectangle.bound hL hS hp hz
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper0CapZeroRectangle.bound hL hS hp hu (by intro he;linarith only [hu.2,he])
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper0CapZeroTriangle.bound hL hS hp hu (by
      intro he
      have hm := mul_nonneg hu.1 (sub_nonneg.mpr hp.1)
      nlinarith only [he,hu.2,hm])
theorem LineUpper1 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailLineRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-1757/5000) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper1HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper1CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper1HeadZeroTriangle.bound hL hS hp hu
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper1HeadCapBoundaryTriangle.bound hL hS hp hu
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper1HeadZeroRectangle.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.LineUpper1HeadCapBoundaryRectangle.bound hL hS hp hz
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper1CapZeroRectangle.bound hL hS hp hu (by intro he;linarith only [hu.2,he])
  · intro p hp u hu
    exact StaticHighMassTailLinks.Before97.LineUpper1CapZeroTriangle.bound hL hS hp hu (by
      intro he
      have hm := mul_nonneg hu.1 (sub_nonneg.mpr hp.1)
      nlinarith only [he,hu.2,hm])
theorem CurvedLower0 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailCurvedRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-3589/10000) (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower0HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower0CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower0HeadZero.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower0HeadCapBoundary.bound hL hS hp hz
theorem CurvedLower1 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailCurvedRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-1757/5000) (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower1HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower1CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower1HeadZero.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedLower1HeadCapBoundary.bound hL hS hp hz
theorem CurvedUpper0 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailCurvedRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-3589/10000) (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper0HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper0CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper0HeadZero.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper0HeadCapBoundary.bound hL hS hp hz
theorem CurvedUpper1 
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000)) : LargeTailCurvedRegionSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) (-1757/5000) (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)) := by
  constructor
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper1HeadSquare.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper1CapFlat.bound hL hS hp hz (by ring_nf;norm_num)
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper1HeadZero.bound hL hS hp hz
  · intro p hp z hz
    exact StaticHighMassTailLinks.Before97.CurvedUpper1HeadCapBoundary.bound hL hS hp hz
end OptimalG.Certificates.StaticHighMassTailBeforeSigns
