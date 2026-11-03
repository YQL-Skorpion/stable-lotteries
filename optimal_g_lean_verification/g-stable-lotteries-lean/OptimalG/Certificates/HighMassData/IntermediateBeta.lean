import OptimalG.Certificates.TensorBernstein

namespace OptimalG.Certificates.HighMassData.IntermediateBeta
open Set
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def numerator (lam S p : ℝ) : ℝ :=
  (2483/500)*lam*p
    + (-2483/500)*S
    + (-2483/1000)*p^2
    + -1*p

def numeratorCertificate : TensorBernstein3 := [
    ⟨(175941057627/1600000000000), 0, 1, 0, 1, 0, 2⟩,
    ⟨(105801057627/800000000000), 0, 1, 0, 1, 1, 1⟩,
    ⟨(64031487/20000000000), 0, 1, 0, 1, 2, 0⟩,
    ⟨(170886861467/1600000000000), 0, 1, 1, 0, 0, 2⟩,
    ⟨(100746861467/800000000000), 0, 1, 1, 0, 1, 1⟩,
    ⟨(170807/4000000000), 0, 1, 1, 0, 2, 0⟩,
    ⟨(879816988373/8000000000000), 1, 0, 0, 1, 0, 2⟩,
    ⟨(264562848127/2000000000000), 1, 0, 0, 1, 1, 1⟩,
    ⟨(64354277/20000000000), 1, 0, 0, 1, 2, 0⟩,
    ⟨(854546007573/8000000000000), 1, 0, 1, 0, 0, 2⟩,
    ⟨(251927357727/2000000000000), 1, 0, 1, 0, 1, 1⟩,
    ⟨(47073/800000000), 1, 0, 1, 0, 2, 0⟩]

theorem numeratorCertificate_checked : numeratorCertificate.check=true := by decide +kernel

theorem numerator_identity (x y z : ℝ) :
    numerator ((22493/40000)+(1/200000)*x) ((227179/10000000)+(6361/10000000)*y) ((22493/40000)+(3507/40000)*z)=(170807/4000000000)+numeratorCertificate.eval x y z := by
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
  have hm : (0:ℝ)<(170807/4000000000) := by norm_num
  linarith only [hh,he,hm]

end OptimalG.Certificates.HighMassData.IntermediateBeta
