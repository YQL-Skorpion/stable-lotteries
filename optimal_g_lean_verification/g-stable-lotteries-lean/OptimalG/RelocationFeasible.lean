import OptimalG.RelocationEnvelope
import OptimalG.SecondRawControl
import OptimalG.EnvelopeFlowFromRaw

/-! Final B.1 assembly after the two concrete continuation comparisons. Every
low-envelope, cap, selection, and determinant input is derived here from the
actual normalized necessary primitive and the certified LP bounds. -/
namespace OptimalG.Relocation
open Set Variational

variable {lam : ℝ} {phi : ℝ → ℝ} (h : NormalizedNecessaryTwoClass lam phi)
include h

/-- A concrete second-phase signed trajectory with the inherited binary tests
supplies a genuinely feasible variational datum via the recovered envelope. -/
theorem feasible_of_second_trajectory (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {Y : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc zStart zEnd))
    (hYD : ∀ z ∈ Ico zStart zEnd,
      HasDerivWithinAt Y (rawVectorField lam (secondExtendedPrimitive lam phi) phi z (Y z)) (Ici z) z)
    (hYlo : ∀ z ∈ Icc zStart zEnd, quadratic lam z-quadratic lam 1 ≤ Y z)
    (hYhi : ∀ z ∈ Icc zStart zEnd, Y z ≤ quadratic lam z-finalScalar lam phi)
    (htests : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(secondPrimitive lam phi (1-z+q)-secondPrimitive lam phi q)/(lam-q) ≤ Y z) :
    Feasible lam := by
  have hd := (recoveredData_admissible h hL hLP).1
  obtain ⟨K,hK⟩ := secondExtended_lipschitz h
  have hphi : ContinuousOn phi (Icc xLo xHi) :=
    h.continuous.mono (Icc_subset_Icc (by norm_num [xLo]) (by norm_num [xHi]))
  apply feasible_of_raw_envelope hd hK hphi (by norm_num : (0 : ℝ) < 0.0519)
    (second_raw_determinant h hL hLP)
    (recoveredData_score_selection h hL hLP)
    (fun _ hr => secondExtended_middle_formula h hL hLP hr)
    (fun _ hp => recoveredData_primitive_dominates h hL hLP hp)
    (fun _ hq => recoveredData_terminal_cap h hL hLP hq)
    hY hYD hYlo hYhi (hYhi zStart (by norm_num [zStart,zEnd]))
  intro z hz q hq
  have hz0 := hz.1
  have hz1 := hz.2
  have hq0 := hq.1
  have hq1 := hq.2
  norm_num [zTest,zEnd,qLo,qHi] at hz0 hz1 hq0 hq1
  have hm : 1-z+q ∈ Icc (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
  have hqI : q ∈ Icc (0 : ℝ) 1 := ⟨by linarith,by linarith⟩
  rw [secondExtended_eq lam phi hm,secondExtended_eq lam phi hqI]
  exact htests z hz q hq

/-- Closed-interval derivative data from the actual continuation existence
proof automatically supplies the continuity and right derivatives above. -/
theorem feasible_of_second_continuation (hL : Certificates.Compact.LambdaRange lam)
    (hLP : UniversalLPPrimitiveBounds phi) {Y : ℝ → ℝ}
    (hYD : ∀ z ∈ Icc zStart zEnd,
      HasDerivWithinAt Y (rawVectorField lam (secondExtendedPrimitive lam phi) phi z (Y z))
        (Icc zStart zEnd) z)
    (hYlo : ∀ z ∈ Icc zStart zEnd, quadratic lam z-quadratic lam 1 ≤ Y z)
    (hYhi : ∀ z ∈ Icc zStart zEnd, Y z ≤ quadratic lam z-finalScalar lam phi)
    (htests : ∀ z ∈ Icc zTest zEnd, ∀ q ∈ Icc qLo qHi,
      z*(secondPrimitive lam phi (1-z+q)-secondPrimitive lam phi q)/(lam-q) ≤ Y z) :
    Feasible lam := by
  apply feasible_of_second_trajectory h hL hLP
    (fun z hz => (hYD z hz).continuousWithinAt) ?_ hYlo hYhi htests
  intro z hz
  exact (hYD z ⟨hz.1,hz.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hz)

end OptimalG.Relocation
