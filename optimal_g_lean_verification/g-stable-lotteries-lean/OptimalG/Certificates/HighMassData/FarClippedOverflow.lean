import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.FarClippedOverflow
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (67/10)*lam^2*S
    + (-2219/1000)*lam^2
    + (691/1000)*lam*S^2
    + (-2364157/1000000)*lam*S
    + (2299910739/4000000000)*lam
    + (-691/1000)*S^2
    + (364157/1000000)*S
    + (-191910739/4000000000)

def numeratorCertificate : TensorBernstein3 := [
    ⟨(618379321/400000000000), 0, 2, 0, 2, 0, 0⟩,
    ⟨(1699672593/400000000000), 0, 2, 1, 1, 0, 0⟩,
    ⟨(14876138053/8000000000000), 0, 2, 2, 0, 0, 0⟩,
    ⟨(227484509/50000000000), 1, 1, 0, 2, 0, 0⟩,
    ⟨(100191643/10000000000), 1, 1, 1, 1, 0, 0⟩,
    ⟨(30525148933/8000000000000), 1, 1, 2, 0, 0, 0⟩,
    ⟨(132837089/100000000000), 2, 0, 0, 2, 0, 0⟩,
    ⟨(137252129/50000000000), 2, 0, 1, 1, 0, 0⟩,
    ⟨(60655711/100000000000), 2, 0, 2, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((167/2000)+(73/2000)*x) ((287/2000)+(73/2000)*y) (0+1*z)=(60655711/100000000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc (167/2000) (3/25))
    (hS : S∈Icc (287/2000) (9/50))
    (hp : p∈Icc 0 1) : 0<numerator lam S p := by
  have hx : ((lam-(167/2000))/(73/2000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((167/2000):ℝ)<(3/25)) hL using 1 <;> norm_num
  have hy : ((S-(287/2000))/(73/2000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((287/2000):ℝ)<(9/50)) hS using 1 <;> norm_num
  have hz : ((p-0)/1)∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : (0:ℝ)<1) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-(167/2000))/(73/2000)) ((S-(287/2000))/(73/2000)) ((p-0)/1)
  have ex : (167/2000)+(73/2000)*((lam-(167/2000))/(73/2000))=lam := by ring
  have ey : (287/2000)+(73/2000)*((S-(287/2000))/(73/2000))=S := by ring
  have ez : 0+1*((p-0)/1)=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(60655711/100000000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.FarClippedOverflow
