import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.HeadShift
import OptimalG.Certificates.StaticBinaryData.StationaryBatch000

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.HeadShift
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.HeadShiftLeaf000.exclusionPolynomial.eqCheck (StaticBinaryStationaryModels.HeadShift.matchingPolynomial)=true := by decide +kernel
private theorem identity001 : StaticBinaryData.Stationary.HeadShiftLeaf001.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadShift.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadShift.matchingPolynomial.scale (3148994/998367)))=true := by decide +kernel
private theorem identity002 : StaticBinaryData.Stationary.HeadShiftLeaf002.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.HeadShift.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadShift.matchingPolynomial.scale (5159437/978064)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (31/40) (17/20))
    (hr : r∈Icc 0 (527/2000))
    (hroot : headStationaryLevel L S initial StaticBinaryCentralExpressions.slope r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.HeadShift p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.HeadShift.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.HeadShift.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.headMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.HeadShift.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.HeadShift.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.HeadShift.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.HeadShift.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (31/40) (13/16) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/4000) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    have hn := StaticBinaryData.Stationary.HeadShiftLeaf000.exclusion_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    change StaticBinaryData.Stationary.HeadShiftLeaf000.exclusion p r 0=StaticBinaryStationaryModels.HeadShift.matching p r 0 at he
    rw [hm] at he
    rw [he] at hn
    exact False.elim (lt_irrefl 0 hn)
  · have hbp : p∈Icc (31/40) (13/16) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/4000) (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity001 p r 0
    change StaticBinaryData.Stationary.HeadShiftLeaf001.numerator p r 0=
      (StaticBinaryStationaryModels.HeadShift.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadShift.matchingPolynomial.scale (3148994/998367))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadShiftLeaf001.numerator p r 0=StaticBinaryStationaryModels.HeadShift.numerator p r 0+
      (((3148994/998367):ℚ):ℝ)*StaticBinaryStationaryModels.HeadShift.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadShiftLeaf001.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadShift.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadShiftLeaf001.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadShift.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
  · have hbp : p∈Icc (13/16) (17/20) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc 0 (527/2000) := by
      simpa [StaticBinaryStationaryCoverage.HeadShift.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity002 p r 0
    change StaticBinaryData.Stationary.HeadShiftLeaf002.numerator p r 0=
      (StaticBinaryStationaryModels.HeadShift.numeratorPolynomial.add (StaticBinaryStationaryModels.HeadShift.matchingPolynomial.scale (5159437/978064))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.HeadShiftLeaf002.numerator p r 0=StaticBinaryStationaryModels.HeadShift.numerator p r 0+
      (((5159437/978064):ℚ):ℝ)*StaticBinaryStationaryModels.HeadShift.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.HeadShiftLeaf002.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.HeadShift.denominator p r 0 :=
      StaticBinaryData.Stationary.HeadShiftLeaf002.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.HeadShift.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.HeadShift
