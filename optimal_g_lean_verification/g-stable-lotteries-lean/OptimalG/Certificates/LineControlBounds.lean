import OptimalG.Certificates.LineControlExpressions
import OptimalG.Certificates.LineControlData.Det
import OptimalG.Certificates.LineControlData.SlopeNum
import OptimalG.Certificates.LineControlData.ThetaLo
import OptimalG.Certificates.LineControlData.ThetaHi
import OptimalG.Certificates.LineControlData.AlphaLo
import OptimalG.Certificates.LineControlData.AlphaHi
import OptimalG.Certificates.LineControlData.SlopeLo
import OptimalG.Certificates.LineControlData.CrossLo
import OptimalG.Certificates.LineControlData.CrossHi
import OptimalG.Certificates.LineControlData.ScaleExact

namespace OptimalG.Certificates.LineControl
open Set

theorem denominator_pos {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) : 0<denominator lam S := by
  have hp : (0:ℝ)∈Icc 0 1 := by constructor <;> norm_num
  have hn := LineControlData.Det.numerator_pos hL hS hp
  have hd := LineControlData.Det.denominator_pos hL hS hp
  have he : denominator lam S=LineControlData.Det.numerator lam S 0/
      LineControlData.Det.denominator lam S 0 := by
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.Det.numerator,LineControlData.Det.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem slopeNumerator_pos {lam S : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000)) : 0<slopeNumerator lam S := by
  have hp : (0:ℝ)∈Icc 0 1 := by constructor <;> norm_num
  have hn := LineControlData.SlopeNum.numerator_pos hL hS hp
  have hd := LineControlData.SlopeNum.denominator_pos hL hS hp
  have he : slopeNumerator lam S=LineControlData.SlopeNum.numerator lam S 0/
      LineControlData.SlopeNum.denominator lam S 0 := by
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.SlopeNum.numerator,LineControlData.SlopeNum.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem thetaLo_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<theta lam S := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.ThetaLo.numerator_pos hL hS hp
  have hd := LineControlData.ThetaLo.denominator_pos hL hS hp
  have he : theta lam S=LineControlData.ThetaLo.numerator lam S p/
      LineControlData.ThetaLo.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.ThetaLo.numerator,LineControlData.ThetaLo.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem thetaHi_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<4/5-theta lam S := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.ThetaHi.numerator_pos hL hS hp
  have hd := LineControlData.ThetaHi.denominator_pos hL hS hp
  have he : 4/5-theta lam S=LineControlData.ThetaHi.numerator lam S p/
      LineControlData.ThetaHi.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.ThetaHi.numerator,LineControlData.ThetaHi.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem alphaLo_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<alpha lam S := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.AlphaLo.numerator_pos hL hS hp
  have hd := LineControlData.AlphaLo.denominator_pos hL hS hp
  have he : alpha lam S=LineControlData.AlphaLo.numerator lam S p/
      LineControlData.AlphaLo.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.AlphaLo.numerator,LineControlData.AlphaLo.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem alphaHi_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<3-alpha lam S := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.AlphaHi.numerator_pos hL hS hp
  have hd := LineControlData.AlphaHi.denominator_pos hL hS hp
  have he : 3-alpha lam S=LineControlData.AlphaHi.numerator lam S p/
      LineControlData.AlphaHi.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.AlphaHi.numerator,LineControlData.AlphaHi.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem slopeLo_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<slope lam S-7/10 := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.SlopeLo.numerator_pos hL hS hp
  have hd := LineControlData.SlopeLo.denominator_pos hL hS hp
  have he : slope lam S-7/10=LineControlData.SlopeLo.numerator lam S p/
      LineControlData.SlopeLo.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.SlopeLo.numerator,LineControlData.SlopeLo.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem crossLo_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<crossing lam S-391/500 := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.CrossLo.numerator_pos hL hS hp
  have hd := LineControlData.CrossLo.denominator_pos hL hS hp
  have he : crossing lam S-391/500=LineControlData.CrossLo.numerator lam S p/
      LineControlData.CrossLo.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.CrossLo.numerator,LineControlData.CrossLo.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem crossHi_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (0:ℝ) 1) : 0<81/100-crossing lam S := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.CrossHi.numerator_pos hL hS hp
  have hd := LineControlData.CrossHi.denominator_pos hL hS hp
  have he : 81/100-crossing lam S=LineControlData.CrossHi.numerator lam S p/
      LineControlData.CrossHi.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.CrossHi.numerator,LineControlData.CrossHi.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

theorem scaleExact_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : S∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (17/20:ℝ) (7/8)) : 0<p*(1-p)-(129/100)*(Variational.quadratic lam p-S-slope lam S*(p-crossing lam S)^2/2) := by
  have hD := denominator_pos hL hS
  have hN := slopeNumerator_pos hL hS
  have hn := LineControlData.ScaleExact.numerator_pos hL hS hp
  have hd := LineControlData.ScaleExact.denominator_pos hL hS hp
  have he : p*(1-p)-(129/100)*(Variational.quadratic lam p-S-slope lam S*(p-crossing lam S)^2/2)=LineControlData.ScaleExact.numerator lam S p/
      LineControlData.ScaleExact.denominator lam S p := by
    dsimp only [theta,alpha,slope,crossing]
    field_simp [hD.ne',hN.ne',hd.ne']
    norm_num [slopeNumerator,denominator,Variational.quadratic,
      LineControlData.ScaleExact.numerator,LineControlData.ScaleExact.denominator]
    <;> ring
  rw [he]
  exact div_pos hn hd

end OptimalG.Certificates.LineControl
