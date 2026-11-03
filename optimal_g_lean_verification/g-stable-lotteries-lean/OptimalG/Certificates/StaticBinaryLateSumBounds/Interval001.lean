import OptimalG.Certificates.StaticBinaryData.LateBatch004
import OptimalG.Certificates.StaticBinaryLateScore

namespace OptimalG.Certificates.StaticBinaryLateSumBounds.Interval001
open Set StaticBinaryCentralExpressions StaticBinaryLateExpressions StaticBinaryLateScalars
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
noncomputable def pieceSum (q : ℝ) : ℝ := (50/3)*(scoreHead (q+(1/150))+scoreCap (q+(1/75))+scoreCap (q+(1/50)))-B*(L-q)+1/2
theorem identity {q : ℝ} (hq : q∈Icc (1/4:ℝ) (337/1000)) :
    StaticBinaryData.LateSum.Interval001.numerator q 0 0=StaticBinaryData.LateSum.Interval001.denominator q 0 0*pieceSum q := by
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
  norm_num [StaticBinaryData.LateSum.Interval001.numerator,StaticBinaryData.LateSum.Interval001.numeratorPolynomial,
    StaticBinaryData.LateSum.Interval001.denominator,StaticBinaryData.LateSum.Interval001.denominatorPolynomial,
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
  field_simp [hx0,hx1,hx2]
  <;> ring

theorem bound {q : ℝ} (hq : q∈Icc (1501/6000) (1541/6000)) : 0≤rightSum q := by
  have hdomain : q∈Icc (1/4:ℝ) (337/1000) := by constructor <;> linarith only [hq.1,hq.2]
  have hn := StaticBinaryData.LateSum.Interval001.numerator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have hd := StaticBinaryData.LateSum.Interval001.denominator_pos (u:=0) (v:=0) hq (by constructor <;> norm_num) (by constructor <;> norm_num)
  have he := identity hdomain
  have hsum : 0≤pieceSum q := by
    by_contra hnle
    have hp := mul_neg_of_pos_of_neg hd (lt_of_not_ge hnle)
    linarith only [hn,he,hp]
  have hv0 : scoreHead (q+(1/150))≤score (q+(1/150)) := by
    exact (score_head (by linarith only [hq.2] : q+(1/150)≤(527/2000:ℝ))).symm.le
  have hv1 : scoreCap (q+(1/75))≤score (q+(1/75)) := by
    apply (score_cap (r:=q+(1/75)) ?_).symm.le
    constructor
    · linarith only [hq.1]
    · norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hq.2]
  have hv2 : scoreCap (q+(1/50))≤score (q+(1/50)) := by
    apply (score_cap (r:=q+(1/50)) ?_).symm.le
    constructor
    · linarith only [hq.1]
    · norm_num [c,StaticLow.leftContact,UpperProfileData.leftContact]
      linarith only [hq.2]
  unfold pieceSum at hsum
  unfold rightSum
  linarith only [hsum,hv0,hv1,hv2]
end OptimalG.Certificates.StaticBinaryLateSumBounds.Interval001
