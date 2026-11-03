import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.CapShift
import OptimalG.Certificates.StaticBinaryData.StationaryBatch006

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.CapShift
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.CapShiftLeaf000.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.CapShift.numeratorPolynomial.add (StaticBinaryStationaryModels.CapShift.matchingPolynomial.scale (5939955/993638)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (849/1000) (73/80))
    (hr : r∈Icc (527/2000) (1459/5000))
    (hroot : Variational.stationaryLevel L S r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.CapShift p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.CapShift.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.CapShift.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.capMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.CapShift.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.CapShift.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.CapShift.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.CapShift.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (849/1000) (73/80) := by
      simpa [StaticBinaryStationaryCoverage.CapShift.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/2000) (1459/5000) := by
      simpa [StaticBinaryStationaryCoverage.CapShift.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    change StaticBinaryData.Stationary.CapShiftLeaf000.numerator p r 0=
      (StaticBinaryStationaryModels.CapShift.numeratorPolynomial.add (StaticBinaryStationaryModels.CapShift.matchingPolynomial.scale (5939955/993638))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.CapShiftLeaf000.numerator p r 0=StaticBinaryStationaryModels.CapShift.numerator p r 0+
      (((5939955/993638):ℚ):ℝ)*StaticBinaryStationaryModels.CapShift.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.CapShiftLeaf000.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.CapShift.denominator p r 0 :=
      StaticBinaryData.Stationary.CapShiftLeaf000.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<1)
      (by norm_num : (0:ℝ)<1) hn hd
      (StaticBinaryStationaryModels.CapShift.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.CapShift
