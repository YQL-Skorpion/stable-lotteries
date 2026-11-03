import OptimalG.Certificates.StaticBinaryStationaryBounds.HeadShift
import OptimalG.Certificates.StaticBinaryStationaryBounds.HeadZero
import OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyLeft
import OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyRight
import OptimalG.Certificates.StaticBinaryStationaryBounds.HeadLate
import OptimalG.Certificates.StaticBinaryStationaryBounds.CapShift
import OptimalG.Certificates.StaticBinaryStationaryBounds.CapZero
import OptimalG.Certificates.StaticBinaryStationaryBounds.CapCurvature

namespace OptimalG.Certificates
open Set StaticBinaryCentralExpressions

set_option maxHeartbeats 0

/-- The root equation is used exactly, through rational polynomial equality
multipliers. All stationary comparisons cover their entire stated intervals. -/
theorem static_binary_stationary_intervals :
    BinaryStationaryIntervals L S initial StaticBinaryCentralExpressions.slope
      StaticHigh.contact StaticHigh.contactValue StaticHigh.contactScore := by
  constructor
  · norm_num [headStationaryLevel,headStationaryConstant,
      StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
      SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
      Variational.cap,Variational.capScore,L,S,StaticLow.lam,StaticLow.slack]
  · norm_num [Variational.stationaryLevel,Variational.capSlack,Variational.capDeficit,
      Variational.cap,Variational.capScore,Variational.quadratic,L,S,StaticLow.lam,StaticLow.slack]
  · intro p hp r hr hroot
    have hh := StaticBinaryStationaryBounds.HeadShift.positive hp hr hroot
    unfold StaticBinaryStationaryExpressions.HeadShift at hh
    linarith only [hh]
  · intro p hp r hr hroot
    have hh := StaticBinaryStationaryBounds.HeadZero.positive hp hr hroot
    unfold StaticBinaryStationaryExpressions.HeadZero at hh
    linarith only [hh]
  · intro p hp r hr hroot
    by_cases hcut : p≤391/500
    · have hh := StaticBinaryStationaryBounds.HeadEarlyLeft.positive ⟨hp.1,hcut⟩ hr hroot
      unfold StaticBinaryStationaryExpressions.HeadEarlyLeft StaticBinaryStationaryExpressions.headBarrier at hh
      rw [max_eq_right (sub_nonpos.mpr hcut)]
      norm_num
      linarith only [hh]
    · have hh := StaticBinaryStationaryBounds.HeadEarlyRight.positive
        ⟨(lt_of_not_ge hcut).le,hp.2⟩ hr hroot
      unfold StaticBinaryStationaryExpressions.HeadEarlyRight StaticBinaryStationaryExpressions.headBarrier at hh
      rw [max_eq_left (sub_nonneg.mpr (lt_of_not_ge hcut).le)]
      linarith only [hh]
  · intro p hp r hr hroot
    have hh := StaticBinaryStationaryBounds.HeadLate.positive ⟨hp.1.le,hp.2.le⟩ hr hroot
    unfold StaticBinaryStationaryExpressions.HeadLate StaticBinaryStationaryExpressions.headBarrier at hh
    linarith only [hh]
  · intro p hp r hr hroot
    have hh := StaticBinaryStationaryBounds.CapShift.positive hp hr hroot
    unfold StaticBinaryStationaryExpressions.CapShift at hh
    linarith only [hh]
  · intro p hp r hr hroot
    have hh := StaticBinaryStationaryBounds.CapZero.positive hp hr hroot
    unfold StaticBinaryStationaryExpressions.CapZero at hh
    linarith only [hh]
  · intro p hp r hr hroot
    have hpp : p∈Icc (86242083/100000000:ℝ) (73/80) := by
      constructor
      · simpa [StaticHigh.contact] using hp.1.le
      · exact hp.2.le
    have hh := StaticBinaryStationaryBounds.CapCurvature.positive hpp hr hroot
    unfold StaticBinaryStationaryExpressions.CapCurvature at hh
    linarith only [hh]

end OptimalG.Certificates
