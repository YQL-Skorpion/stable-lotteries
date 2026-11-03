import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.IntermediateMargin
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (4000/527)*lam^2*p
    + (-9676000000/1143447183)*lam*S*p
    + (-5581/1054)*lam*p
    + 1*S
    + (-1/2)*p^2
    + 1*p

def numeratorCertificate : TensorBernstein3 := [
    ⟨(208350326809844039/6098384976000000000), 0, 2, 0, 1, 0, 2⟩,
    ⟨(11839676513805391/254099374000000000), 0, 2, 0, 1, 1, 1⟩,
    ⟨(65453818292213/7622981220000000), 0, 2, 0, 1, 2, 0⟩,
    ⟨(605548713934670153/18295154928000000000), 0, 2, 1, 0, 0, 2⟩,
    ⟨(202149251603344747/4573788732000000000), 0, 2, 1, 0, 1, 1⟩,
    ⟨(33182931953891/4573788732000000), 0, 2, 1, 0, 2, 0⟩,
    ⟨(1250258795357626871/18295154928000000000), 1, 1, 0, 1, 0, 2⟩,
    ⟨(55008114189134611/590166288000000000), 1, 1, 0, 1, 1, 1⟩,
    ⟨(785899037948141/45737887320000000), 1, 1, 0, 1, 2, 0⟩,
    ⟨(6056269927417047967/91475774640000000000), 1, 1, 1, 0, 0, 2⟩,
    ⟨(8087657688812370317/91475774640000000000), 1, 1, 1, 0, 1, 1⟩,
    ⟨(664111057381937/45737887320000000), 1, 1, 1, 0, 2, 0⟩,
    ⟨(15630195422006083247/457378873200000000000), 2, 0, 0, 1, 0, 2⟩,
    ⟨(10659935438473144061/228689436600000000000), 2, 0, 0, 1, 1, 1⟩,
    ⟨(14455004920447/1681539975000000), 2, 0, 0, 1, 2, 0⟩,
    ⟨(1682514648613577823/50819874800000000000), 2, 0, 1, 0, 0, 2⟩,
    ⟨(3370560564824007547/76229812200000000000), 2, 0, 1, 0, 1, 1⟩,
    ⟨(138450726451801/19057453050000000), 2, 0, 1, 0, 2, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((22493/40000)+(3507/40000)*z)=(33182931953891/4573788732000000)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(33182931953891/4573788732000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.IntermediateMargin
