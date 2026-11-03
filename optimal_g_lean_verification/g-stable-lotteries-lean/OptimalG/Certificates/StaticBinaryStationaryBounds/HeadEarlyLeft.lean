import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.HeadEarlyLeft
import OptimalG.Certificates.StaticBinaryData.StationaryBatch001
import OptimalG.Certificates.StaticBinaryData.StationaryBatch002
import OptimalG.Certificates.StaticBinaryData.StationaryBatch003

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyLeft
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf000.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial)=true := by decide +kernel
private theorem identity001 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf001.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1953814/969183)))=true := by decide +kernel
private theorem identity002 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf002.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity003 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf003.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-873902/437443)))=true := by decide +kernel
private theorem identity004 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf004.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity005 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf005.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial)=true := by decide +kernel
private theorem identity006 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf006.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1047519/526799)))=true := by decide +kernel
private theorem identity007 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf007.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity008 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf008.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-914071/460722)))=true := by decide +kernel
private theorem identity009 : StaticBinaryData.Stationary.HeadEarlyLeftLeaf009.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (31/40) (391/500))
    (hr : r∈Icc 0 (527/2000))
    (hroot : headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.HeadEarlyLeft p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.HeadEarlyLeft.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.headMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.HeadEarlyLeft.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.HeadEarlyLeft.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (31/40) (1557/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf000.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf000.exclusion p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (31/40) (3107/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity001 p r 0
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf001.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1953814/969183))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf001.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.numerator p r 0+
      (((-1953814/969183):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf001.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyLeft.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyLeftLeaf001.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1/2))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyLeft.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (31/40) (3107/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity002 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf002.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf002.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (3107/4000) (1557/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity003 p r 0
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf003.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-873902/437443))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf003.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.numerator p r 0+
      (((-873902/437443):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf003.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyLeft.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyLeftLeaf003.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1/2))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyLeft.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (3107/4000) (1557/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity004 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf004.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf004.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (1557/2000) (391/500) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity005 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf005.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf005.exclusion p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (1557/2000) (3121/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity006 p r 0
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf006.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-1047519/526799))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf006.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.numerator p r 0+
      (((-1047519/526799):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf006.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyLeft.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyLeftLeaf006.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1/2))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyLeft.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (1557/2000) (3121/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity007 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf007.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf007.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (3121/4000) (391/500) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity008 p r 0
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf008.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyLeft.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyLeft.matchingPolynomial.scale (-914071/460722))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf008.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyLeft.numerator p r 0+
      (((-914071/460722):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf008.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyLeft.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyLeftLeaf008.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1/2))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyLeft.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (3121/4000) (391/500) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyLeft.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity009 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyLeftLeaf009.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyLeftLeaf009.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyLeft.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
end OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyLeft
