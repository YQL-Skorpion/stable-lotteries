import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.FarClippedHead
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (-691/2000)*lam^2
    + (-2659/1000)*lam*p
    + (691/2000)*lam
    + (309/1000)*p

def numeratorCertificate : TensorBernstein3 := [
    ⟨(967641/25000000), 0, 2, 0, 0, 0, 1⟩,
    ⟨(3225357/50000000), 0, 2, 0, 0, 1, 0⟩,
    ⟨(767961/12500000), 1, 1, 0, 0, 0, 1⟩,
    ⟨(863967/10000000), 1, 1, 0, 0, 1, 0⟩,
    ⟨(443901/25000000), 2, 0, 0, 0, 0, 1⟩,
    ⟨(422859/25000000), 2, 0, 0, 0, 1, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator (0+(3/25)*x) (0+1*y) ((9/50)+(167/2000)*z)=(422859/25000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc 0 (3/25))
    (hS : S∈Icc 0 1)
    (hp : p∈Icc (9/50) (527/2000)) : 0<numerator lam S p := by
  have hx : ((lam-0)/(3/25))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<(3/25)) hL using 1 <;> norm_num
  have hy : ((S-0)/1)∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<1) hS using 1 <;> norm_num
  have hz : ((p-(9/50))/(167/2000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((9/50):ℝ)<(527/2000)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-0)/(3/25)) ((S-0)/1) ((p-(9/50))/(167/2000))
  have ex : 0+(3/25)*((lam-0)/(3/25))=lam := by ring
  have ey : 0+1*((S-0)/1)=S := by ring
  have ez : (9/50)+(167/2000)*((p-(9/50))/(167/2000))=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(422859/25000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.FarClippedHead
