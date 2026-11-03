import OptimalG.Certificates.StaticBinaryStationaryDomain
import OptimalG.Certificates.StaticBinaryStationaryCoverage
import OptimalG.Certificates.StaticBinaryStationaryModels.CapCurvature
import OptimalG.Certificates.StaticBinaryData.StationaryBatch006

namespace OptimalG.Certificates.StaticBinaryStationaryBounds.CapCurvature
open Set StaticBinaryCentralExpressions
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
private theorem identity000 : StaticBinaryData.Stationary.CapCurvatureLeaf000.numeratorPolynomial.eqCheck (StaticBinaryStationaryModels.CapCurvature.numeratorPolynomial.add (StaticBinaryStationaryModels.CapCurvature.matchingPolynomial.scale (713/955487)))=true := by decide +kernel
theorem positive {p r : ℝ} (hp : p∈Icc (86242083/100000000) (73/80))
    (hr : r∈Icc (527/2000) (1459/5000))
    (hroot : Variational.stationaryLevel L S r=(1-p)^2) :
    0<StaticBinaryStationaryExpressions.CapCurvature p r := by
  have hdom := StaticBinaryStationaryExpressions.domain_nonzero
    (show r∈Icc (0:ℝ) (1459/5000) by constructor <;> linarith only [hr.1,hr.2])
  have hm : StaticBinaryStationaryModels.CapCurvature.matching p r 0=0 := by
    rw [StaticBinaryStationaryModels.CapCurvature.matching_eq p r 0 hdom.1]
    simp only [StaticBinaryStationaryExpressions.capMatch,hroot,sub_self,mul_zero]
  have hx : ∀ i,(StaticBinaryStationaryCoverage.CapCurvature.rootBox i).Contains (![p,r] i) := by
    intro i
    fin_cases i
    · simpa [StaticBinaryStationaryCoverage.CapCurvature.rootBox,RatInterval.Contains] using hp
    · simpa [StaticBinaryStationaryCoverage.CapCurvature.rootBox,RatInterval.Contains] using hr
  obtain ⟨j,hj⟩ := StaticBinaryStationaryCoverage.CapCurvature.covered ![p,r] hx
  fin_cases j
  · have hbp : p∈Icc (86242083/100000000) (73/80) := by
      simpa [StaticBinaryStationaryCoverage.CapCurvature.leafBoxes,RatInterval.Contains] using hj 0
    have hbr : r∈Icc (527/2000) (1459/5000) := by
      simpa [StaticBinaryStationaryCoverage.CapCurvature.leafBoxes,RatInterval.Contains] using hj 1
    have he := RationalPolynomial3.eqCheck_sound identity000 p r 0
    change StaticBinaryData.Stationary.CapCurvatureLeaf000.numerator p r 0=
      (StaticBinaryStationaryModels.CapCurvature.numeratorPolynomial.add (StaticBinaryStationaryModels.CapCurvature.matchingPolynomial.scale (713/955487))).eval p r 0 at he
    rw [RationalPolynomial3.eval_add,RationalPolynomial3.eval_scale] at he
    change StaticBinaryData.Stationary.CapCurvatureLeaf000.numerator p r 0=StaticBinaryStationaryModels.CapCurvature.numerator p r 0+
      (((713/955487):ℚ):ℝ)*StaticBinaryStationaryModels.CapCurvature.matching p r 0 at he
    rw [hm,mul_zero,add_zero] at he
    have hn := StaticBinaryData.Stationary.CapCurvatureLeaf000.numerator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    rw [he] at hn
    have hd : 0<StaticBinaryStationaryModels.CapCurvature.denominator p r 0 :=
      StaticBinaryData.Stationary.CapCurvatureLeaf000.denominator_pos (u:=0) hbp hbr (by constructor <;> norm_num)
    exact StaticBinaryStationaryExpressions.positive_of_scaled
      (by norm_num : (0:ℝ)<131416353501132795093951233808496562589438591112546844474985900000000000000000000000000000000)
      (by norm_num : (0:ℝ)<6086750666092310038945258550378984164711507077422566609607226860743433714915000000000000000) hn hd
      (StaticBinaryStationaryModels.CapCurvature.expression_eq p r 0 hdom.1 hdom.2.1 hdom.2.2)
end OptimalG.Certificates.StaticBinaryStationaryBounds.CapCurvature
