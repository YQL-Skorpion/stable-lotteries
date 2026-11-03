import OptimalG.ParameterTransferContinuation
import OptimalG.ParameterTransferDerivative
import OptimalG.RawFeatureSupport
import OptimalG.ContinuousODERegularity

/-! The complete analytic upward-parameter construction of B.2. The low
primitive and score are explicit; this record packages the constructed high
trajectory and its actual support-point and terminal inequalities. -/
namespace OptimalG.Variational.ParameterTransfer
open Set MeasureTheory

structure UpwardTransfer (lam delta : ℝ) (d : LowRankData) (Y : ℝ → ℝ) where
  trajectory : ℝ → ℝ
  initial : trajectory zStart=quadratic (lam+delta) zStart-scalar d.S delta
  derivative : ∀ z ∈ Icc zStart zEnd,HasDerivWithinAt trajectory
    (rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z (trajectory z)) (Icc zStart zEnd) z
  absolutelyContinuous : AbsolutelyContinuousOnInterval trajectory zStart zEnd
  lower : ∀ z ∈ Icc zStart zEnd,quadratic (lam+delta) z-quadratic (lam+delta) 1 ≤ trajectory z
  upper : ∀ z ∈ Icc zStart zEnd,trajectory z ≤ quadratic (lam+delta) z-scalar d.S delta
  gain : ∀ z ∈ Icc zStart zEnd,Y z+0.26412*delta ≤ trajectory z
  terminal : ∀ z ∈ Icc zTest zEnd,∀ q ∈ Icc qLo qHi,
    z*(shiftedPrimitive lam d delta (1-z+q)-shiftedPrimitive lam d delta q)/(lam+delta-q)+
      0.07812*delta ≤ trajectory z
  support : ∀ z u,∀ v ∈ controlFeatureSupport d,
    rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z u ≤
      rawFeatureH (lam+delta) (shiftedPrimitive lam d delta) z u v

theorem exists_upwardTransfer {lam delta : ℝ} {d : LowRankData} {Y : ℝ → ℝ}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) (hY : IsContinuation lam d Y) (htest : PassesTerminalTests lam d Y) :
    Nonempty (UpwardTransfer lam delta d Y) := by
  obtain ⟨Z,hZ0,hZD,hZB,hZT⟩ := exists_shifted_continuation h hLnew hd hY htest
  obtain ⟨K,hK,htime⟩ := shifted_regular h hLnew hd
  have hAC := continuous_ode_solution_absolutelyContinuous
    (by norm_num [zStart,zEnd] : zStart ≤ zEnd) hK (htime 0).continuousOn hZD
  refine ⟨⟨Z,hZ0,hZD,hAC,fun z hz => (hZB z hz).2.1,fun z hz => (hZB z hz).2.2,
    fun z hz => (hZB z hz).1,hZT,?_⟩⟩
  intro z u v hv
  exact rawVectorField_le_feature h (shiftedPrimitive_lipschitz h delta)
    (fun c hc => shifted_determinant h hLnew hd hc) z u hv

end OptimalG.Variational.ParameterTransfer
