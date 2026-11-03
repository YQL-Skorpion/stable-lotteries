import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.RatioMiddle
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (-1720000/723243)*lam*S
    + (-71/200)*lam
    + (47103/200000)

def numeratorCertificate : TensorBernstein3 := [
    ⟨(11502274441/3616215000000), 0, 1, 0, 1, 0, 0⟩,
    ⟨(5617398681/2410810000000), 0, 1, 1, 0, 0, 0⟩,
    ⟨(153265050529/48216200000000), 1, 0, 0, 1, 0, 0⟩,
    ⟨(67349400143/28929720000000), 1, 0, 1, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) (0+1*z)=(67349400143/28929720000000)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(67349400143/28929720000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.RatioMiddle
