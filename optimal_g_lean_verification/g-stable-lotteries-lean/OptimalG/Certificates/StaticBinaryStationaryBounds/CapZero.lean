import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.CapZero
import OptimalG.Certificates.StaticBinaryData.StationaryBatch006

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.CapZero
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.CapZeroLeaf000.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.CapZero.numeratorPolynomial.add (StaticBinaryStationaryModels.CapZero.matchingPolynomial.scale (329877/578021)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (849/1000) (73/80))
    (hr : r∈Icc (527/2000) (1459/5000))
    (hroot : Variational.stationaryLevel L S r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.CapZero p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.CapZero.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.CapZero.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.capMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.CapZero.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.CapZero.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.CapZero.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.CapZero.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (849/1000) (73/80) := by
      simpa [StaticBinaryStationaryCoverage.CapZero.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/2000) (1459/5000) := by
      simpa [StaticBinaryStationaryCoverage.CapZero.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    change StaticBinaryData.Stationary.CapZeroLeaf000.numerator p r 0=
      (StaticBinaryStationaryModels.CapZero.numeratorPolynomial.add (StaticBinaryStationaryModels.CapZero.matchingPolynomial.scale (329877/578021))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.CapZeroLeaf000.numerator p r 0=StaticBinaryStationaryModels.CapZero.numerator p r 0+
      (((329877/578021):ℚ):ℝ)*StaticBinaryStationaryModels.CapZero.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.CapZeroLeaf000.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.CapZero.denominator p r 0 :=
      StaticBinaryData.Stationary.CapZeroLeaf000.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<819437878441850172740210569189124870439200000000000)
      (by norm_num : (0:ℝ)<1012915182006552329592044400000000000000000000000000) hn hd
      (StaticBinaryStationaryModels.CapZero.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.CapZero
