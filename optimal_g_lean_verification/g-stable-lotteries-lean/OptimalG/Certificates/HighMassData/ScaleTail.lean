import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.ScaleTail
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (1072575/236672)*p^3
    + (-62836517/5916800)*p^2
    + (46945781/5916800)*p
    + (-10923639/5916800)

def numeratorCertificate : TensorBernstein3 := [
    ⟨(2431931593/1893376000000), 0, 0, 0, 0, 0, 3⟩,
    ⟨(626203113/236672000000), 0, 0, 0, 0, 1, 2⟩,
    ⟨(43497887/29584000000), 0, 0, 0, 0, 2, 1⟩,
    ⟨(809547/7396000000), 0, 0, 0, 0, 3, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((7/8)+(1/200)*z)=(809547/7396000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (7/8) (22/25)) : 0<numerator lam S p := by
  have hx : ((lam-(22493/40000))/(1/200000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(56233/100000)) hL using 1 <;> norm_num
  have hy : ((S-(227179/10000000))/(6361/10000000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((227179/10000000):ℝ)<(11677/500000)) hS using 1 <;> norm_num
  have hz : ((p-(7/8))/(1/200))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((7/8):ℝ)<(22/25)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-(22493/40000))/(1/200000)) ((S-(227179/10000000))/(6361/10000000)) ((p-(7/8))/(1/200))
  have ex : (22493/40000)+(1/200000)*((lam-(22493/40000))/(1/200000))=lam := by ring
  have ey : (227179/10000000)+(6361/10000000)*((S-(227179/10000000))/(6361/10000000))=S := by ring
  have ez : (7/8)+(1/200)*((p-(7/8))/(1/200))=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(809547/7396000000) := by norm_num
  linarith only [hh,he,hm]

noncomputable def denominator (lam S p : ℝ) : ℝ :=
  1

def denominatorCertificate : TensorBernstein3 := [
    ⟨(1/2), 0, 0, 0, 0, 0, 0⟩]

theorem denominatorCertificate_checked : denominatorCertificate.check=true := by decide +kernel

theorem denominator_identity (x y z : ℝ) :
    denominator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((7/8)+(1/200)*z)=(1/2)+denominatorCertificate.eval x y z := by
  norm_num [denominator,denominatorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem denominator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (7/8) (22/25)) : 0<denominator lam S p := by
  have hx : ((lam-(22493/40000))/(1/200000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(56233/100000)) hL using 1 <;> norm_num
  have hy : ((S-(227179/10000000))/(6361/10000000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((227179/10000000):ℝ)<(11677/500000)) hS using 1 <;> norm_num
  have hz : ((p-(7/8))/(1/200))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((7/8):ℝ)<(22/25)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound denominatorCertificate_checked hx hy hz
  have he := denominator_identity ((lam-(22493/40000))/(1/200000)) ((S-(227179/10000000))/(6361/10000000)) ((p-(7/8))/(1/200))
  have ex : (22493/40000)+(1/200000)*((lam-(22493/40000))/(1/200000))=lam := by ring
  have ey : (227179/10000000)+(6361/10000000)*((S-(227179/10000000))/(6361/10000000))=S := by ring
  have ez : (7/8)+(1/200)*((p-(7/8))/(1/200))=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(1/2) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.ScaleTail
