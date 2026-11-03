import OptimalG.Certificates.StaticHighMassTailLinkBatch11
import OptimalG.Certificates.StaticHighMassTailLinks.LateHead.MiddleUpper0Cap
import OptimalG.Certificates.StaticHighMassTailLinkBatch12
import OptimalG.Certificates.StaticHighMassTailLinkBatch13
import OptimalG.Certificates.StaticHighMassTailLinkBatch14
import OptimalG.Certificates.StaticHighMassTailLinkBatch15
import OptimalG.Certificates.StaticHighMassTailLinkBatch16

namespace OptimalG.Certificates.StaticHighMassTailLateSigns
open Set LargeTailExpressions
theorem MiddleUpper0 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  constructor
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.MiddleUpper0Head.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.MiddleUpper0Cap.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.MiddleUpper0Cone.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.MiddleUpper0NearLine.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.MiddleUpper0Line.bound hlam hS hp hz hr hq
theorem MiddleUpper1 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (13/20) (391/500))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  constructor
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.MiddleUpper1Head.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.MiddleUpper1Head.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.MiddleUpper1Cap.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.MiddleUpper1Cap.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.MiddleUpper1Cone.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.MiddleUpper1Cone.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.MiddleUpper1NearLine.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.MiddleUpper1NearLine.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.MiddleUpper1Line.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.MiddleUpper1Line.target]
theorem CurvedUpper0 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  constructor
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedUpper0Head.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedUpper0Cap.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedUpper0Cone.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedUpper0NearLine.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedUpper0Line.bound hlam hS hp hz hr hq
theorem CurvedUpper1 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massCap (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  constructor
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedUpper1Head.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedUpper1Head.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedUpper1Cap.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedUpper1Cap.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedUpper1Cone.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedUpper1Cone.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedUpper1NearLine.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedUpper1NearLine.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedUpper1Line.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedUpper1Line.target]
theorem CurvedLower0 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-3589/10000) := by
  constructor
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedLower0Head.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedLower0Cap.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedLower0Cone.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedLower0NearLine.bound hlam hS hp hz hr hq
  · intro r hr hq
    exact StaticHighMassTailLinks.LateHead.CurvedLower0Line.bound hlam hS hp hz hr hq
theorem CurvedLower1 {p z : ℝ}
    (hlam : (StaticLow.lam:ℝ)∈Icc (22493/40000) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (391/500) (41/50))
    (hz : z∈Icc (97/100) 1)
    : LargeTailLateHeadSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p (massLower (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p) z (8793/100000) (-1757/5000) := by
  constructor
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedLower1Head.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedLower1Head.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedLower1Cap.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedLower1Cap.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedLower1Cone.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedLower1Cone.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedLower1NearLine.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedLower1NearLine.target]
  · intro r hr hq
    convert! StaticHighMassTailLinks.LateHead.CurvedLower1Line.bound hlam hS hp hz hr hq using 1 <;>
      norm_num [StaticHighMassTailModels.LateHead.CurvedLower1Line.target]
end OptimalG.Certificates.StaticHighMassTailLateSigns
