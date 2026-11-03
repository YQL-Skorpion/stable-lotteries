import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.HeadEarlyRight
import OptimalG.Certificates.StaticBinaryData.StationaryBatch003
import OptimalG.Certificates.StaticBinaryData.StationaryBatch004
import OptimalG.Certificates.StaticBinaryData.StationaryBatch005

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyRight
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.HeadEarlyRightLeaf000.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial)=true := by decide +kernel
private theorem identity001 : StaticBinaryData.Stationary.HeadEarlyRightLeaf001.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-237112/223629)))=true := by decide +kernel
private theorem identity002 : StaticBinaryData.Stationary.HeadEarlyRightLeaf002.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity003 : StaticBinaryData.Stationary.HeadEarlyRightLeaf003.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-644332/606165)))=true := by decide +kernel
private theorem identity004 : StaticBinaryData.Stationary.HeadEarlyRightLeaf004.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity005 : StaticBinaryData.Stationary.HeadEarlyRightLeaf005.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial)=true := by decide +kernel
private theorem identity006 : StaticBinaryData.Stationary.HeadEarlyRightLeaf006.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-792327/743717)))=true := by decide +kernel
private theorem identity007 : StaticBinaryData.Stationary.HeadEarlyRightLeaf007.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-1))=true := by decide +kernel
private theorem identity008 : StaticBinaryData.Stationary.HeadEarlyRightLeaf008.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-878740/824279)))=true := by decide +kernel
private theorem identity009 : StaticBinaryData.Stationary.HeadEarlyRightLeaf009.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-1))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (391/500) (807/1000))
    (hr : r∈Icc 0 (527/2000))
    (hroot : headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.HeadEarlyRight p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.HeadEarlyRight.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.headMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.HeadEarlyRight.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.HeadEarlyRight.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (391/500) (1589/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf000.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf000.exclusion p r 0=StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (391/500) (3153/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity001 p r 0
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf001.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-237112/223629))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf001.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyRight.numerator p r 0+
      (((-237112/223629):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf001.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyRight.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyRightLeaf001.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(2246746806292134704653182587731354687/2402550241951025449696500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyRight.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (391/500) (3153/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity002 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf002.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf002.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (3153/4000) (1589/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity003 p r 0
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf003.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-644332/606165))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf003.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyRight.numerator p r 0+
      (((-644332/606165):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf003.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyRight.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyRightLeaf003.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(2246746806292134704653182587731354687/2402550241951025449696500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyRight.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (3153/4000) (1589/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity004 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf004.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf004.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (1589/2000) (807/1000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity005 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf005.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf005.exclusion p r 0=StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (1589/2000) (3203/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity006 p r 0
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf006.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-792327/743717))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf006.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyRight.numerator p r 0+
      (((-792327/743717):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf006.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyRight.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyRightLeaf006.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(2246746806292134704653182587731354687/2402550241951025449696500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyRight.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (1589/2000) (3203/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity007 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf007.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf007.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (3203/4000) (807/1000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (1581/8000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity008 p r 0
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf008.numerator p r 0=
      (StaticBinaryStationaryModels.HeadEarlyRight.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadEarlyRight.matchingPolynomial.scale (-878740/824279))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf008.numerator p r 0=StaticBinaryStationaryModels.HeadEarlyRight.numerator p r 0+
      (((-878740/824279):ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf008.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadEarlyRight.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadEarlyRightLeaf008.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(2246746806292134704653182587731354687/2402550241951025449696500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadEarlyRight.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (3203/4000) (807/1000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (1581/8000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadEarlyRight.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity009 p r 0
    have hn := StaticBinaryData.Stationary.HeadEarlyRightLeaf009.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadEarlyRightLeaf009.exclusion p r 0=((-1:ℚ):ℝ)*StaticBinaryStationaryModels.HeadEarlyRight.matching p r 0 at he
    rw [hm,mul_zero] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
end OptimalG.Certificates.StaticBinaryStationaryBounds.HeadEarlyRight
