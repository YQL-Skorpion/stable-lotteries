import OptimalG.Certificates.StaticBinaryStationaryExpressions

namespace OptimalG.Certificates.StaticBinaryStationaryExpressions
open Set StaticBinaryCentralExpressions

theorem domain_nonzero {r : ℝ} (hr : r∈Icc (0:ℝ) (1459/5000)) :
    r≠1 ∧ r≠L ∧ (1-r)^3-2*L*S≠0 := by
  have hL : (1/2:ℝ)<L := by norm_num [L,StaticLow.lam]
  have hx : (7/10:ℝ)≤1-r := by linarith only [hr.2]
  have hx0 : 0≤1-r := by linarith only [hx]
  have hp := mul_nonneg (sub_nonneg.mpr hx)
    (show 0≤(1-r)^2+(7/10)*(1-r)+(7/10)^2 by positivity)
  have hsmall : 2*L*S≤3/100 := by norm_num [L,S,StaticLow.lam,StaticLow.slack]
  refine ⟨by linarith only [hr.2],by linarith only [hr.2,hL],?_⟩
  have hpos : 0<(1-r)^3-2*L*S := by nlinarith only [hp,hsmall]
  exact hpos.ne'

theorem positive_of_scaled {ns ds N D T : ℝ}
    (hns : 0<ns) (hds : 0<ds) (hN : 0<N) (hD : 0<D)
    (he : ns*N=ds*D*T) : 0<T := by
  have hn := mul_pos hns hN
  have hd := mul_pos hds hD
  by_contra hbad
  have hh := mul_nonpos_of_nonneg_of_nonpos hd.le (le_of_not_gt hbad)
  linarith only [he,hn,hh]

end OptimalG.Certificates.StaticBinaryStationaryExpressions
