import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.HeadLate
import OptimalG.Certificates.StaticBinaryData.StationaryBatch005
import OptimalG.Certificates.StaticBinaryData.StationaryBatch006

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.HeadLate
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.HeadLateLeaf000.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.matchingPolynomial)=true := by decide +kernel
private theorem identity001 : StaticBinaryData.Stationary.HeadLateLeaf001.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (892677/866363)))=true := by decide +kernel
private theorem identity002 : StaticBinaryData.Stationary.HeadLateLeaf002.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (93578/123667)))=true := by decide +kernel
private theorem identity003 : StaticBinaryData.Stationary.HeadLateLeaf003.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.matchingPolynomial)=true := by decide +kernel
private theorem identity004 : StaticBinaryData.Stationary.HeadLateLeaf004.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (707675/804672)))=true := by decide +kernel
private theorem identity005 : StaticBinaryData.Stationary.HeadLateLeaf005.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (1246865/997587)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (807/1000) (17/20))
    (hr : r∈Icc 0 (527/2000))
    (hroot : headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.HeadLate p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.HeadLate.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.HeadLate.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.headMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.HeadLate.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.HeadLate.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.HeadLate.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.HeadLate.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (807/1000) (1657/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    have hn := StaticBinaryData.Stationary.HeadLateLeaf000.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadLateLeaf000.exclusion p r 0=StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (807/1000) (3271/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity001 p r 0
    change StaticBinaryData.Stationary.HeadLateLeaf001.numerator p r 0=
      (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (892677/866363))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadLateLeaf001.numerator p r 0=StaticBinaryStationaryModels.HeadLate.numerator p r 0+
      (((892677/866363):ℚ):ℝ)*StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadLateLeaf001.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadLate.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadLateLeaf001.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<137448466881662656662647720477311086217370363015456408508384286425000000000000000000000000)
      (by norm_num : (0:ℝ)<100404104837054215738937478932176155585752807506301611251509136169846800000000000000000000) hn hd
      (StaticBinaryStationaryModels.HeadLate.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (807/1000) (3271/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity002 p r 0
    change StaticBinaryData.Stationary.HeadLateLeaf002.numerator p r 0=
      (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (93578/123667))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadLateLeaf002.numerator p r 0=StaticBinaryStationaryModels.HeadLate.numerator p r 0+
      (((93578/123667):ℚ):ℝ)*StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadLateLeaf002.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadLate.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadLateLeaf002.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<137448466881662656662647720477311086217370363015456408508384286425000000000000000000000000)
      (by norm_num : (0:ℝ)<100404104837054215738937478932176155585752807506301611251509136169846800000000000000000000) hn hd
      (StaticBinaryStationaryModels.HeadLate.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (3271/4000) (1657/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity003 p r 0
    have hn := StaticBinaryData.Stationary.HeadLateLeaf003.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadLateLeaf003.exclusion p r 0=StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (3271/4000) (1657/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity004 p r 0
    change StaticBinaryData.Stationary.HeadLateLeaf004.numerator p r 0=
      (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (707675/804672))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadLateLeaf004.numerator p r 0=StaticBinaryStationaryModels.HeadLate.numerator p r 0+
      (((707675/804672):ℚ):ℝ)*StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadLateLeaf004.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadLate.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadLateLeaf004.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<137448466881662656662647720477311086217370363015456408508384286425000000000000000000000000)
      (by norm_num : (0:ℝ)<100404104837054215738937478932176155585752807506301611251509136169846800000000000000000000) hn hd
      (StaticBinaryStationaryModels.HeadLate.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (1657/2000) (17/20) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadLate.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity005 p r 0
    change StaticBinaryData.Stationary.HeadLateLeaf005.numerator p r 0=
      (StaticBinaryStationaryModels.HeadLate.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadLate.matchingPolynomial.scale (1246865/997587))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadLateLeaf005.numerator p r 0=StaticBinaryStationaryModels.HeadLate.numerator p r 0+
      (((1246865/997587):ℚ):ℝ)*StaticBinaryStationaryModels.HeadLate.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadLateLeaf005.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadLate.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadLateLeaf005.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<137448466881662656662647720477311086217370363015456408508384286425000000000000000000000000)
      (by norm_num : (0:ℝ)<100404104837054215738937478932176155585752807506301611251509136169846800000000000000000000) hn hd
      (StaticBinaryStationaryModels.HeadLate.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.HeadLate
