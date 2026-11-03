import OptimalG.Certificates.StaticBinaryData.LateBatch005
import OptimalG.Certificates.StaticBinaryLateScore

namespace OptimalG.Certificates.StaticBinaryLateSumBounds.Interval008
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def pieceSum (q : ℝ) : ℝ := (50/3)*((0:ℝ)+(0:ℝ)+(0:ℝ))-B*(L-q)+1/2
theorem identity {q : ℝ} (hq : q∈Icc (1/4:ℝ) (337/1000)) :
    StaticBinaryData.LateSum.Interval008.numerator q 0 0=StaticBinaryData.LateSum.Interval008.denominator q 0 0*pieceSum q := by
  norm_num [pieceSum,StaticBinaryData.LateSum.Interval008.numerator,StaticBinaryData.LateSum.Interval008.numeratorPolynomial,
    StaticBinaryData.LateSum.Interval008.denominator,StaticBinaryData.LateSum.Interval008.denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]
  <;> ring

theorem bound {q : ℝ} (hq : q∈Icc (10832058923715861924746186956795033139730291770574117586303419872020842075114404805648103816025163381332179591774815095891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000) (337/1000)) : 0≤rightSum q := by
  have hdomain : q∈Icc (1/4:ℝ) (337/1000) := by constructor <;> linarith only [hq.1,hq.2]
  have hn := StaticBinaryData.LateSum.Interval008.numerator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have hd := StaticBinaryData.LateSum.Interval008.denominator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have he := identity hdomain
  have hsum : 0≤pieceSum q := by
    by_contra hnle
    have hp := mul_neg_of_pos_of_neg hd (lt_of_not_ge hnle)
    linarith only [hn,he,hp]
  have hv0 : (0:ℝ)≤score (q+(1/150)) := by
    simpa only [score_zero (r:=q+(1/150)) (by norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]; linarith only [hq.1])] using (le_rfl : (0:ℝ)≤0)
  have hv1 : (0:ℝ)≤score (q+(1/75)) := by
    simpa only [score_zero (r:=q+(1/75)) (by norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]; linarith only [hq.1])] using (le_rfl : (0:ℝ)≤0)
  have hv2 : (0:ℝ)≤score (q+(1/50)) := by
    simpa only [score_zero (r:=q+(1/50)) (by norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]; linarith only [hq.1])] using (le_rfl : (0:ℝ)≤0)
  unfold pieceSum at hsum
  unfold rightSum
  linarith only [hsum,hv0,hv1,hv2]
end OptimalG.Certificates.StaticBinaryLateSumBounds.Interval008
