import OptimalG.Certificates.StaticBinaryInputs
import OptimalG.BinaryAllMass

/-! Final analytic assembly of C.3 for the explicit rational upper curve. -/
namespace OptimalG.Certificates.StaticBinaryAssembly
open Set Variational StaticBinaryCentralExpressions StaticBinaryLateScalars

set_option maxHeartbeats 0

theorem binary
    (hterminal : ∀ p∈Icc (21/25:ℝ) (7/8),∀ q∈Icc (26/100:ℝ) (28/100),
      terminalBound L S p q≤StaticBinaryInputs.Y p)
    (hdeficit : ∀ p∈Icc (31/40:ℝ) (807/1000),
      quadratic L p-S-StaticBinaryInputs.Y p≤(399/500)*(max (p-391/500) 0)^2)
    (hcontrol : ∀ p∈Ioo (807/1000:ℝ) StaticContact.entry,
      StaticCurve.score p≤highAffineControl L S (29/100)
        (capDiagonalTheta L S (29/100) (1459/5000))
        (capDiagonalAlpha L S (29/100) (1459/5000)) StaticBinaryInputs.Y p)
    (small : BinarySmallIntervals L S initial slope (527/2000) c)
    (stationary : BinaryStationaryIntervals L S initial slope
      StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore)
    (late : BinaryLateIntervals L S initial slope c (348541/1000000)
      (87/1000000000) (24/100000) B C 3) :
    ∀ p∈Ioo (0:ℝ) 1,∀ q∈Icc (0:ℝ) p,
      normalizedBinaryTest StaticCurve.score p q≤L := by
  apply StaticCurve.binaryGeometry.binary_all_mass StaticCurve.verifierCurve StaticCurve.concave
    (Y:=StaticBinaryInputs.Y) (dY:=StaticCurve.score)
    (b:=StaticContact.entry) (z:=(StaticHigh.contact:ℝ))
    (qs:=(StaticHigh.contactRank:ℝ)) (T:=(StaticHigh.contactValue:ℝ))
    (H:=(StaticHigh.contactScore:ℝ)) (B:=B) (C:=C) (n:=3)
  · norm_num [StaticLow.slack]
  · constructor <;> linarith only [StaticContact.entry_mem.1,StaticContact.entry_mem.2]
  · exact StaticContact.entry_le_contact
  · norm_num [StaticHigh.contact]
  · norm_num [StaticHigh.contactRank]
  · simpa only [StaticCurve.initial_value,StaticContact.initial,
      show (0.2635:ℝ)=527/2000 by norm_num] using StaticContact.entry_identity
  · exact StaticContact.contact_stationary
  · exact StaticCurve.contact_values.2.trans StaticContact.contact_value
  · exact StaticCurve.contact_values.1.trans StaticContact.contact_score
  · intro p hp
    exact StaticBinaryInputs.actual hp.2
  · intro p hp
    exact (StaticCurve.tail_values hp).1
  · intro p hp
    exact (StaticCurve.tail_values hp).2
  · exact StaticBinaryInputs.continuous
  · intro p hp
    exact StaticBinaryInputs.derivative hp
  · exact hterminal
  · exact hdeficit
  · exact hcontrol
  · exact StaticBinaryInputs.slack_pos
  · rw [StaticBinaryInputs.reference_values.1]
    norm_num
  · rw [StaticBinaryInputs.reference_values.2]
    norm_num
  · exact tail_majorant.1
  · exact tail_majorant.2.1
  · exact tail_majorant.2.2
  · simpa only [StaticBinaryInputs.initial,StaticBinaryInputs.slope,L,S,c] using small
  · simpa only [StaticBinaryInputs.initial,StaticBinaryInputs.slope,L,S,c] using stationary
  · simpa only [StaticBinaryInputs.initial,StaticBinaryInputs.slope,L,S,c] using late

end OptimalG.Certificates.StaticBinaryAssembly
