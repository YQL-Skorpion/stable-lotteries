import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.LineControlData.AlphaHi
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  96250*lam^2
    + -281250*lam*S
    + -86700*lam
    + 101250*S
    + 20061

def numeratorCertificate : TensorBernstein3 := [
    ⟨(777659383/3200000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(21178571/102400), 0, 2, 1, 0, 0, 0⟩,
    ⟨(31111225929/64000000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(2647800711/6400000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(15558038423/64000000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(13241400389/64000000), 2, 0, 1, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(21178571/102400)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(21178571/102400) := by norm_num
  linarith only [hh,he,hm]

noncomputable def denominator (lam S p : ℝ) : ℝ :=
  42500*lam^2
    + -93750*lam*S
    + -28900*lam
    + 33750*S
    + 5337

def denominatorCertificate : TensorBernstein3 := [
    ⟨(13477506219/12800000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(5329227/5120), 0, 2, 1, 0, 0, 0⟩,
    ⟨(134780427893/64000000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(6661801081/3200000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(33696448433/32000000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(16655171047/16000000), 2, 0, 1, 0, 0, 0⟩]

theorem denominatorCertificate_checked : denominatorCertificate.check=true := by decide +kernel

theorem denominator_identity (x y z : ℝ) :
    denominator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(5329227/5120)+denominatorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(5329227/5120) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.LineControlData.AlphaHi
