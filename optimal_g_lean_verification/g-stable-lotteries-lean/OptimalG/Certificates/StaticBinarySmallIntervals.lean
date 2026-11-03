import OptimalG.Certificates.StaticBinaryCentralBound
import OptimalG.Certificates.BinarySmallData.HeadZero
import OptimalG.Certificates.BinarySmallData.MiddleZero
import OptimalG.Certificates.BinarySmallData.DerivativeMargin
import OptimalG.Certificates.BinarySmallData.CentralAnchor
import OptimalG.CompletedCurveFacts

/-! The complete small/central scalar package for the explicit upper curve. -/
namespace OptimalG.Certificates
open Set StaticBinaryCentralExpressions

set_option maxHeartbeats 0

theorem static_binary_small_intervals {phi : ℝ → ℝ}
    (h : VerifierCurve phi L)
    (g : BinaryCurveGeometry phi L S slope c) :
    BinarySmallIntervals L S (phi 0) slope (527/2000) c := by
  have hinit : phi 0=initial := g.initial_eq
  have hL : L∈Icc (22493/40000:ℝ) (56233/100000) := by norm_num [L,StaticLow.lam]
  have hS : S∈Icc (227179/10000000:ℝ) (11677/500000) := by norm_num [S,StaticLow.slack]
  constructor
  · intro p hp
    have hh := BinarySmallData.HeadZero.numerator_pos hL hS hp
    rw [BinarySmallData.HeadZero.expression_identity] at hh
    change 0<L*(initial+slope*p/2)-(Variational.quadratic L (1-p)-S) at hh
    rw [hinit]
    linarith only [hh]
  · intro p hp
    have hh := BinarySmallData.MiddleZero.numerator_pos hL hS hp
    rw [BinarySmallData.MiddleZero.expression_identity] at hh
    linarith only [hh]
  · intro p hp
    have hp' : p∈Icc (43767/100000:ℝ) (13/20) := by
      refine ⟨?_,hp.2⟩
      have hh := hp.1
      norm_num [L,StaticLow.lam] at hh
      exact hh
    have hh := BinarySmallData.DerivativeMargin.numerator_pos hL hS hp'
    rw [BinarySmallData.DerivativeMargin.expression_identity] at hh
    change 0≤p*(1+phi 0-2*L)-p^2/2+S
    rw [hinit]
    exact hh.le
  · intro p hp
    have hh := BinarySmallData.CentralAnchor.numerator_pos hL hS hp
    rw [BinarySmallData.CentralAnchor.expression_identity] at hh
    rw [hinit]
    change 0 < -(Variational.quadratic L p-S+p*(L-9/50-1+p-initial-slope*(9/50))) at hh
    linarith only [hh]
  · intro p hp q hq
    rw [hinit]
    change q*base p q+p*actualError p q≤0
    apply StaticBinaryCentralBound.bound hp hq
    unfold actualError
    rw [←hinit]
    exact g.headCapError_nonpos h ⟨by linarith only [hp.2,hq.1],by linarith only [hp.1,hq.2]⟩

end OptimalG.Certificates
