import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.LineControlData.ThetaHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  13750*lam^2
    + -62500*lam*S
    + -17225*lam
    + 22500*S
    + 6183

def numeratorCertificate : TensorBernstein3 := [
    ⟨(4524928351/16000000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(8792458837/32000000), 0, 2, 1, 0, 0, 0⟩,
    ⟨(3619840891/6400000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(4396100591/8000000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(2262336941/8000000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(4395971769/16000000), 2, 0, 1, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(4395971769/16000000)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(4395971769/16000000) := by norm_num
  linarith only [hh,he,hm]

noncomputable def denominator (lam S p : ℝ) : ℝ :=
  212500*lam^2
    + -468750*lam*S
    + -144500*lam
    + 168750*S
    + 26685

def denominatorCertificate : TensorBernstein3 := [
    ⟨(13477506219/2560000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(5329227/1024), 0, 2, 1, 0, 0, 0⟩,
    ⟨(134780427893/12800000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(6661801081/640000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(33696448433/6400000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(16655171047/3200000), 2, 0, 1, 0, 0, 0⟩]

theorem denominatorCertificate_checked : denominatorCertificate.check=true := by decide +kernel

theorem denominator_identity (x y z : ℝ) :
    denominator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(5329227/1024)+denominatorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(5329227/1024) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.LineControlData.ThetaHi
