import OptimalG.Certificates.StaticBinaryLateArea
import OptimalG.Certificates.StaticBinaryLateRightSum

namespace OptimalG.Certificates
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars

/-- All late scalar obligations are actual exact rational certificates for
this explicit candidate, including the continuum of ranks and widths. -/
theorem static_binary_late_intervals :
    BinaryLateIntervals L S initial StaticBinaryCentralExpressions.slope c
      (348541/1000000) (87/1000000000) (24/100000) B C 3 := by
  constructor
  · norm_num
  · exact bound_pos.le
  · intro d hd
    exact width_nonneg hd
  · intro d hd
    exact width_high hd
  · intro d hd q hq
    exact StaticBinaryLateArea.bound hd hq
  · exact small_rank
  · exact endpoint_bound
  · intro q hq
    have he := rightSum_eq q
    norm_num only [Nat.cast_ofNat] at he ⊢
    rw [he]
    exact StaticBinaryLateRightSum.nonneg hq

end OptimalG.Certificates
