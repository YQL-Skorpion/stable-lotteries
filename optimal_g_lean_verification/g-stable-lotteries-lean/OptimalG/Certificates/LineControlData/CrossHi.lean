import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.LineControlData.CrossHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  -3125000*lam^2*S
    + -1125000*lam^2
    + 3656250*lam*S
    + 1123425*lam
    + -911250*S
    + -278478

def numeratorCertificate : TensorBernstein3 := [
    ⟨(68775414942187/128000000000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(40762809092481/64000000000), 0, 2, 1, 0, 0, 0⟩,
    ⟨(8591383399869/8000000000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(40740649644431/32000000000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(34343357814269/64000000000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(40718488279611/64000000000), 2, 0, 1, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(34343357814269/64000000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc 0 1) : 0<numerator lam S p := by
  have hx : ((lam-(22493/40000))/(1/200000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(56233/100000)) hL using 1 <;> norm_num
  have hy : ((S-(227179/10000000))/(6361/10000000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((227179/10000000):ℝ)<(11677/500000)) hS using 1 <;> norm_num
  have hz : ((p-0)/1)∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<1) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-(22493/40000))/(1/200000)) ((S-(227179/10000000))/(6361/10000000)) ((p-0)/1)
  have ex : (22493/40000)+(1/200000)*((lam-(22493/40000))/(1/200000))=lam := by ring
  have ey : (227179/10000000)+(6361/10000000)*((S-(227179/10000000))/(6361/10000000))=S := by ring
  have ez : 0+1*((p-0)/1)=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(34343357814269/64000000000) := by norm_num
  linarith only [hh,he,hm]

noncomputable def denominator (lam S p : ℝ) : ℝ :=
  3125000*lam*S
    + 922500*lam
    + -1125000*S
    + -376200

def denominatorCertificate : TensorBernstein3 := [
    ⟨(20084295647/256000), 0, 1, 0, 1, 0, 0⟩,
    ⟨(20187254793/256000), 0, 1, 1, 0, 0, 0⟩,
    ⟨(100427836593/1280000), 1, 0, 0, 1, 0, 0⟩,
    ⟨(20188529009/256000), 1, 0, 1, 0, 0, 0⟩]

theorem denominatorCertificate_checked : denominatorCertificate.check=true := by decide +kernel

theorem denominator_identity (x y z : ℝ) :
    denominator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(20084295647/256000)+denominatorCertificate.eval x y z := by
  norm_num [denominator,denominatorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem denominator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc 0 1) : 0<denominator lam S p := by
  have hx : ((lam-(22493/40000))/(1/200000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(56233/100000)) hL using 1 <;> norm_num
  have hy : ((S-(227179/10000000))/(6361/10000000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((227179/10000000):ℝ)<(11677/500000)) hS using 1 <;> norm_num
  have hz : ((p-0)/1)∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<1) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound denominatorCertificate_checked hx hy hz
  have he := denominator_identity ((lam-(22493/40000))/(1/200000)) ((S-(227179/10000000))/(6361/10000000)) ((p-0)/1)
  have ex : (22493/40000)+(1/200000)*((lam-(22493/40000))/(1/200000))=lam := by ring
  have ey : (227179/10000000)+(6361/10000000)*((S-(227179/10000000))/(6361/10000000))=S := by ring
  have ez : 0+1*((p-0)/1)=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(20084295647/256000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.LineControlData.CrossHi
