import OptimalG.Certificates.StaticHighMassTailHighSigns
import OptimalG.Certificates.StaticHighMassTailBeforeSigns
import OptimalG.Certificates.StaticHighMassTailLateSigns
import OptimalG.LargeTailVerification
import OptimalG.LargeTailCornerSelection

namespace OptimalG.Certificates
open Set LargeTailExpressions

theorem staticLargeTail_corner_signs {p z : ℝ}
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (13/20:ℝ) (41/50)) (hz : z∈Icc (7/8:ℝ) 1) :
    LargeTailCornerSigns (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p z := by
  constructor
  · intro hz97
    apply largeTail_corner_selection
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.LineUpper0 hL hS).cover ⟨hp.1,hcut⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.LineUpper0 hL hS ⟨hp.1,hcut⟩ hz)
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.LineUpper1 hL hS).cover ⟨hp.1,hcut⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.LineUpper1 hL hS ⟨hp.1,hcut⟩ hz)
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.CurvedLower0 hL hS).cover ⟨hcut,hp.2⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.CurvedLower0 hL hS ⟨hcut,hp.2⟩ hz)
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.CurvedLower1 hL hS).cover ⟨hcut,hp.2⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.CurvedLower1 hL hS ⟨hcut,hp.2⟩ hz)
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.CurvedUpper0 hL hS).cover ⟨hcut,hp.2⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.CurvedUpper0 hL hS ⟨hcut,hp.2⟩ hz)
    · intro hcut
      exact (StaticHighMassTailBeforeSigns.CurvedUpper1 hL hS).cover ⟨hcut,hp.2⟩ ⟨hz.1,hz97⟩
        (StaticHighMassTailHighSigns.CurvedUpper1 hL hS ⟨hcut,hp.2⟩ hz)
  · apply largeTail_corner_selection
    · intro hcut
      exact StaticHighMassTailHighSigns.LineUpper0 hL hS ⟨hp.1,hcut⟩ hz
    · intro hcut
      exact StaticHighMassTailHighSigns.LineUpper1 hL hS ⟨hp.1,hcut⟩ hz
    · intro hcut
      exact StaticHighMassTailHighSigns.CurvedLower0 hL hS ⟨hcut,hp.2⟩ hz
    · intro hcut
      exact StaticHighMassTailHighSigns.CurvedLower1 hL hS ⟨hcut,hp.2⟩ hz
    · intro hcut
      exact StaticHighMassTailHighSigns.CurvedUpper0 hL hS ⟨hcut,hp.2⟩ hz
    · intro hcut
      exact StaticHighMassTailHighSigns.CurvedUpper1 hL hS ⟨hcut,hp.2⟩ hz
  · intro hz97
    apply largeTail_corner_selection
    · intro hcut
      exact StaticHighMassTailLateSigns.MiddleUpper0 hL hS ⟨hp.1,hcut⟩ ⟨hz97,hz.2⟩
    · intro hcut
      exact StaticHighMassTailLateSigns.MiddleUpper1 hL hS ⟨hp.1,hcut⟩ ⟨hz97,hz.2⟩
    · intro hcut
      exact StaticHighMassTailLateSigns.CurvedLower0 hL hS ⟨hcut,hp.2⟩ ⟨hz97,hz.2⟩
    · intro hcut
      exact StaticHighMassTailLateSigns.CurvedLower1 hL hS ⟨hcut,hp.2⟩ ⟨hz97,hz.2⟩
    · intro hcut
      exact StaticHighMassTailLateSigns.CurvedUpper0 hL hS ⟨hcut,hp.2⟩ ⟨hz97,hz.2⟩
    · intro hcut
      exact StaticHighMassTailLateSigns.CurvedUpper1 hL hS ⟨hcut,hp.2⟩ ⟨hz97,hz.2⟩
end OptimalG.Certificates
