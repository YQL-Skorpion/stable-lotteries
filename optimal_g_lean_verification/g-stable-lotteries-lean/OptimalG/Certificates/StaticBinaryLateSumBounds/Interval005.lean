import OptimalG.Certificates.StaticBinaryData.LateBatch005
import OptimalG.Certificates.StaticBinaryLateScore

namespace OptimalG.Certificates.StaticBinaryLateSumBounds.Interval005
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def pieceSum (q : ℝ) : ℝ := (50/3)*(scoreCone (q+(1/150))+scoreCone (q+(1/75))+scoreCone (q+(1/50)))-B*(L-q)+1/2
theorem identity {q : ℝ} (hq : q∈Icc (1/4:ℝ) (337/1000)) :
    StaticBinaryData.LateSum.Interval005.numerator q 0 0=StaticBinaryData.LateSum.Interval005.denominator q 0 0*pieceSum q := by
  have hslack : 0<Variational.capSlack L S c/(309/1000) := by
    norm_num [Variational.capSlack,Variational.capScore,L,S,c,StaticLow.lam,StaticLow.slack,
      StaticLow.leftContact,UpperProfileData.leftContact]
  have hr0 : 1-(q+(1/150))≠0 := by linarith only [hq.2]
  have hc0 : Variational.capSlack L S c/(309/1000)+7189/20000-(q+(1/150))≠0 := by linarith only [hslack,hq.2]
  have hr1 : 1-(q+(1/75))≠0 := by linarith only [hq.2]
  have hc1 : Variational.capSlack L S c/(309/1000)+7189/20000-(q+(1/75))≠0 := by linarith only [hslack,hq.2]
  have hr2 : 1-(q+(1/50))≠0 := by linarith only [hq.2]
  have hc2 : Variational.capSlack L S c/(309/1000)+7189/20000-(q+(1/50))≠0 := by linarith only [hslack,hq.2]
  simp only [pieceSum,scoreHead,scoreCap,scoreCone,Variational.capSlack,Variational.capScore]
  field_simp [hr0,hr1,hr2,hc0,hc1,hc2]
  norm_num [StaticBinaryData.LateSum.Interval005.numerator,StaticBinaryData.LateSum.Interval005.numeratorPolynomial,
    StaticBinaryData.LateSum.Interval005.denominator,StaticBinaryData.LateSum.Interval005.denominatorPolynomial,
    RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]
  ring_nf
  have hx0 : (22201:ℝ)-q*44700+q^2*22500≠0 := by nlinarith [hq.2,sq_nonneg q]
  have hx1 : (5476:ℝ)-q*11100+q^2*5625≠0 := by nlinarith [hq.2,sq_nonneg q]
  have hx2 : (2401:ℝ)-q*4900+q^2*2500≠0 := by nlinarith [hq.2,sq_nonneg q]
  have hcone0 : (84325097958986742618301063580608576087612699439107561727867:ℝ)-q*215073359862566807221090116253695390241527288730000000000000≠0 := by linarith only [hq.2]
  have hcone1 : (248673826679708891710481388416751820458007552542722685183601:ℝ)-q*645220079587700421663270348761086170724581866190000000000000≠0 := by linarith only [hq.2]
  have hcone2 : (244372359482457555566059586091677912653177006768122685183601:ℝ)-q*645220079587700421663270348761086170724581866190000000000000≠0 := by linarith only [hq.2]
  field_simp [hx0,hx1,hx2,hcone0,hcone1,hcone2]
  ring_nf
  have hcone1three : (746021480039126675131444165250255461374022657628168055550803:ℝ)-q*1935660238763101264989811046283258512173745598570000000000000≠0 := by linarith only [hq.2]
  have hcone0scale3 : (252975293876960227854903190741825728262838098317322685183601:ℝ)-q*645220079587700421663270348761086170724581866190000000000000≠0 := by linarith only [hq.2]
  have hcone0scale9 : (758925881630880683564709572225477184788514294951968055550803:ℝ)-q*1935660238763101264989811046283258512173745598570000000000000≠0 := by linarith only [hq.2]
  have hcone1scale3 : (746021480039126675131444165250255461374022657628168055550803:ℝ)-q*1935660238763101264989811046283258512173745598570000000000000≠0 := by linarith only [hq.2]
  have hcone1scale9 : (2238064440117380025394332495750766384122067972884504166652409:ℝ)-q*5806980716289303794969433138849775536521236795710000000000000≠0 := by linarith only [hq.2]
  have hcone2scale3 : (733117078447372666698178758275033737959531020304368055550803:ℝ)-q*1935660238763101264989811046283258512173745598570000000000000≠0 := by linarith only [hq.2]
  have hcone2scale9 : (2199351235342118000094536274825101213878593060913104166652409:ℝ)-q*5806980716289303794969433138849775536521236795710000000000000≠0 := by linarith only [hq.2]
  field_simp [hcone0,hcone1,hcone2,hcone1three,hcone0scale3,hcone0scale9,hcone1scale3,hcone1scale9,hcone2scale3,hcone2scale9]
  <;> ring

theorem bound {q : ℝ} (hq : q∈Icc (8652805016133667/30000000000000000) (10395848796186841646603236307354207299655183079759224261720018193160081900315912026656070581952701238282841191774815095891/32715759564676520860721298708061938005633151811116999343755125914557013109886958424402492555434660728700380000000000000000)) : 0≤rightSum q := by
  have hdomain : q∈Icc (1/4:ℝ) (337/1000) := by constructor <;> linarith only [hq.1,hq.2]
  have hn := StaticBinaryData.LateSum.Interval005.numerator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have hd := StaticBinaryData.LateSum.Interval005.denominator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have he := identity hdomain
  have hsum : 0≤pieceSum q := by
    by_contra hnle
    have hp := mul_neg_of_pos_of_neg hd (lt_of_not_ge hnle)
    linarith only [hn,he,hp]
  have hv0 : scoreCone (q+(1/150))≤score (q+(1/150)) := by
    apply score_cone_le
    constructor
    · norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hq.1]
    · norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]
      linarith only [hq.2]
  have hv1 : scoreCone (q+(1/75))≤score (q+(1/75)) := by
    apply score_cone_le
    constructor
    · norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hq.1]
    · norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]
      linarith only [hq.2]
  have hv2 : scoreCone (q+(1/50))≤score (q+(1/50)) := by
    apply score_cone_le
    constructor
    · norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hq.1]
    · norm_num [StaticBinaryLateExpressions.cutoff,binaryAreaCutoff,
    StaticBinaryCentralExpressions.L,StaticBinaryCentralExpressions.S,StaticBinaryCentralExpressions.c,
    StaticBinaryCentralExpressions.initial,StaticBinaryCentralExpressions.slope,
    StaticLow.lam,StaticLow.slack,StaticLow.leftContact,UpperProfileData.leftContact,
    SmallMassExpressions.initial,SmallMassExpressions.slope,headInitial,headSlope,
    Variational.cap,Variational.capScore,Variational.capSlack,Variational.capDeficit,Variational.quadratic,
    StaticBinaryLateScalars.B,StaticHigh.tailSlope]
      linarith only [hq.2]
  unfold pieceSum at hsum
  unfold rightSum
  linarith only [hsum,hv0,hv1,hv2]
end OptimalG.Certificates.StaticBinaryLateSumBounds.Interval005
