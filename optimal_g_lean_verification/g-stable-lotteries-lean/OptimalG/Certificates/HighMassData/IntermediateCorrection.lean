import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.IntermediateCorrection
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  -1*lam^2*p
    + 1*lam*S
    + (-1/2)*lam*p^2
    + (11/10)*lam*p
    + -1*S*p
    + (-1/10)*S
    + (-1/2)*p^3
    + (19/20)*p^2
    + (-1/2)*p

def numeratorCertificate : TensorBernstein3 := [
    ⟨(29550197021511/6400000000000000), 0, 2, 0, 1, 0, 3⟩,
    ⟨(120928559121483/6400000000000000), 0, 2, 0, 1, 1, 2⟩,
    ⟨(144614411547033/6400000000000000), 0, 2, 0, 1, 2, 1⟩,
    ⟨(51079411204911/6400000000000000), 0, 2, 0, 1, 3, 0⟩,
    ⟨(29143093021511/6400000000000000), 0, 2, 1, 0, 0, 3⟩,
    ⟨(119350318689483/6400000000000000), 0, 2, 1, 0, 1, 2⟩,
    ⟨(142679242683033/6400000000000000), 0, 2, 1, 0, 2, 1⟩,
    ⟨(50315378772911/6400000000000000), 0, 2, 1, 0, 3, 0⟩,
    ⟨(14773904525843/1600000000000000), 1, 1, 0, 1, 0, 3⟩,
    ⟨(60460285901739/1600000000000000), 1, 1, 0, 1, 1, 2⟩,
    ⟨(144605539325253/3200000000000000), 1, 1, 0, 1, 2, 1⟩,
    ⟨(51076138331311/3200000000000000), 1, 1, 0, 1, 3, 0⟩,
    ⟨(14570357614643/1600000000000000), 1, 1, 1, 0, 0, 3⟩,
    ⟨(59671180952139/1600000000000000), 1, 1, 1, 0, 1, 2⟩,
    ⟨(142670400994053/3200000000000000), 1, 1, 1, 0, 2, 1⟩,
    ⟨(50312116076911/3200000000000000), 1, 1, 1, 0, 3, 0⟩,
    ⟨(29545420991889/6400000000000000), 2, 0, 0, 1, 0, 3⟩,
    ⟨(120912584201529/6400000000000000), 2, 0, 0, 1, 1, 2⟩,
    ⟨(144596666805501/6400000000000000), 2, 0, 0, 1, 2, 1⟩,
    ⟨(51072865353711/6400000000000000), 2, 0, 0, 1, 3, 0⟩,
    ⟨(29138337347089/6400000000000000), 2, 0, 1, 0, 0, 3⟩,
    ⟨(119334404835129/6400000000000000), 2, 0, 1, 0, 1, 2⟩,
    ⟨(142661559007101/6400000000000000), 2, 0, 1, 0, 2, 1⟩,
    ⟨(50308853276911/6400000000000000), 2, 0, 1, 0, 3, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((22493/40000)+(3507/40000)*z)=(29138337347089/6400000000000000)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(29138337347089/6400000000000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.IntermediateCorrection
