import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.HeadZero
import OptimalG.Certificates.StaticBinaryData.StationaryBatch000
import OptimalG.Certificates.StaticBinaryData.StationaryBatch001

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.HeadZero
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.HeadZeroLeaf000.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadZero.matchingPolynomial)=true := by decide +kernel
private theorem identity001 : StaticBinaryData.Stationary.HeadZeroLeaf001.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadZero.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadZero.matchingPolynomial.scale (88172/109769)))=true := by decide +kernel
private theorem identity002 : StaticBinaryData.Stationary.HeadZeroLeaf002.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadZero.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadZero.matchingPolynomial.scale (851245/732078)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (31/40) (17/20))
    (hr : r∈Icc 0 (527/2000))
    (hroot : headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.HeadZero p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.HeadZero.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.HeadZero.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.headMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.HeadZero.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.HeadZero.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.HeadZero.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.HeadZero.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (31/40) (13/16) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    have hn := StaticBinaryData.Stationary.HeadZeroLeaf000.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadZeroLeaf000.exclusion p r 0=StaticBinaryStationaryModels.HeadZero.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (31/40) (13/16) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity001 p r 0
    change StaticBinaryData.Stationary.HeadZeroLeaf001.numerator p r 0=
      (StaticBinaryStationaryModels.HeadZero.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadZero.matchingPolynomial.scale (88172/109769))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadZeroLeaf001.numerator p r 0=StaticBinaryStationaryModels.HeadZero.numerator p r 0+
      (((88172/109769):ℚ):ℝ)*StaticBinaryStationaryModels.HeadZero.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadZeroLeaf001.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadZero.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadZeroLeaf001.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1024297348052312715925263211486406088049/1266143977508190411990055500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadZero.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (13/16) (17/20) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadZero.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity002 p r 0
    change StaticBinaryData.Stationary.HeadZeroLeaf002.numerator p r 0=
      (StaticBinaryStationaryModels.HeadZero.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadZero.matchingPolynomial.scale (851245/732078))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadZeroLeaf002.numerator p r 0=StaticBinaryStationaryModels.HeadZero.numerator p r 0+
      (((851245/732078):ℚ):ℝ)*StaticBinaryStationaryModels.HeadZero.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadZeroLeaf002.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadZero.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadZeroLeaf002.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<(1024297348052312715925263211486406088049/1266143977508190411990055500000000000000))
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadZero.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.HeadZero
