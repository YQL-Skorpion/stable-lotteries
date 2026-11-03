import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.FarClippedNoOverflow
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (-691/1000)*lam^2
    + (2659/500)*lam*S
    + (-1163843/1000000)*lam
    + (-309/500)*S
    + (162843/1000000)

def numeratorCertificate : TensorBernstein3 := [
    ⟨(1952841/12500000), 0, 2, 0, 1, 0, 0⟩,
    ⟨(562341/12500000), 0, 2, 1, 0, 0, 0⟩,
    ⟨(863967/5000000), 1, 1, 0, 1, 0, 0⟩,
    ⟨(325911/5000000), 1, 1, 1, 0, 0, 0⟩,
    ⟨(165393/25000000), 2, 0, 0, 1, 0, 0⟩,
    ⟨(256113/25000000), 2, 0, 1, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator (0+(3/25)*x) (0+(9/50)*y) (0+1*z)=(165393/25000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc 0 (3/25))
    (hS : S∈Icc 0 (9/50))
    (hp : p∈Icc 0 1) : 0<numerator lam S p := by
  have hx : ((lam-0)/(3/25))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<(3/25)) hL using 1 <;> norm_num
  have hy : ((S-0)/(9/50))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<(9/50)) hS using 1 <;> norm_num
  have hz : ((p-0)/1)∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<1) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-0)/(3/25)) ((S-0)/(9/50)) ((p-0)/1)
  have ex : 0+(3/25)*((lam-0)/(3/25))=lam := by ring
  have ey : 0+(9/50)*((S-0)/(9/50))=S := by ring
  have ez : 0+1*((p-0)/1)=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(165393/25000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.FarClippedNoOverflow
