import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.IntermediateEtaZero
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (16000000000/1143447183)*lam^3*S
    + (-2000/527)*lam^3
    + (-38704000000000000/2480970512923407)*lam^2*S^2
    + (-8000000/2169729)*lam^2*S
    + (2927/2108)*lam^2
    + (756800000/1143447183)*lam*S
    + (200/527)*lam

def numeratorCertificate : TensorBernstein3 := [
    ⟨(42216812456550885026283841/6202426282308517500000000000), 0, 3, 0, 2, 0, 0⟩,
    ⟨(60156173168411058650640163/4134950854872345000000000000), 0, 3, 1, 1, 0, 0⟩,
    ⟨(96010134547091660431627307/12404852564617035000000000000), 0, 3, 2, 0, 0, 0⟩,
    ⟨(1012844832854636835690588659/49619410258468140000000000000), 1, 2, 0, 2, 0, 0⟩,
    ⟨(63673715321068865073529127/1459394419366710000000000000), 1, 2, 1, 1, 0, 0⟩,
    ⟨(1151764365759965368999890059/49619410258468140000000000000), 1, 2, 2, 0, 0, 0⟩,
    ⟨(506243080542007292174813347/24809705129234070000000000000), 2, 1, 0, 2, 0, 0⟩,
    ⟨(541047599112241688365453487/12404852564617035000000000000), 2, 1, 1, 1, 0, 0⟩,
    ⟨(575703555650971434418755067/24809705129234070000000000000), 2, 1, 2, 0, 0, 0⟩,
    ⟨(168687913940881630958549761/24809705129234070000000000000), 3, 0, 0, 2, 0, 0⟩,
    ⟨(12019302559225249434527863/826990170974469000000000000), 3, 0, 1, 1, 0, 0⟩,
    ⟨(191841641865161314909252369/24809705129234070000000000000), 3, 0, 2, 0, 0, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((22493/40000)+(3507/40000)*z)=(168687913940881630958549761/24809705129234070000000000000)+numeratorCertificate.eval x y z := by
  norm_num [numerator,numeratorCertificate,TensorBernstein3.eval,TensorBernsteinTerm3.eval]
  <;> ring

theorem numerator_pos {lam S p : ℝ}
    (hL : lam∈Icc (22493/40000) (56233/100000))
    (hS : S∈Icc (227179/10000000) (11677/500000))
    (hp : p∈Icc (22493/40000) (13/20)) : 0<numerator lam S p := by
  have hx : ((lam-(22493/40000))/(1/200000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(56233/100000)) hL using 1 <;> norm_num
  have hy : ((S-(227179/10000000))/(6361/10000000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((227179/10000000):ℝ)<(11677/500000)) hS using 1 <;> norm_num
  have hz : ((p-(22493/40000))/(3507/40000))∈Icc (0:ℝ) 1 := by
    convert normalized_coordinate_mem (by norm_num : ((22493/40000):ℝ)<(13/20)) hp using 1 <;> norm_num
  have hh := TensorBernstein3.check_sound numeratorCertificate_checked hx hy hz
  have he := numerator_identity ((lam-(22493/40000))/(1/200000)) ((S-(227179/10000000))/(6361/10000000)) ((p-(22493/40000))/(3507/40000))
  have ex : (22493/40000)+(1/200000)*((lam-(22493/40000))/(1/200000))=lam := by ring
  have ey : (227179/10000000)+(6361/10000000)*((S-(227179/10000000))/(6361/10000000))=S := by ring
  have ez : (22493/40000)+(3507/40000)*((p-(22493/40000))/(3507/40000))=p := by ring
  rw [ex,ey,ez] at he
  have hm : (0:ℝ)<(168687913940881630958549761/24809705129234070000000000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.IntermediateEtaZero
