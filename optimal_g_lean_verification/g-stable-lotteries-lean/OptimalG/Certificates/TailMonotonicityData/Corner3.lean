import OptimalG.Certificates.TensorBoxReconstruction

namespace OptimalG.Certificates.TailMonotonicityData.Corner3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def polynomial : RationalPolynomial3 := [[[(542276273/4622500000)], [(-9746660637/20353792000)]], [[(-134228171/46225000)], [(1361520559/203537920)], [(26814375/2544224)]], [[(6623/1849)], [(-26814375/2544224)]]]
noncomputable def value (lam S q : ℝ) : ℝ :=
  (-26814375/2544224)*lam^2*S
    + (6623/1849)*lam^2
    + (26814375/2544224)*lam*S^2
    + (1361520559/203537920)*lam*S
    + (-134228171/46225000)*lam
    + (-9746660637/20353792000)*S
    + (542276273/4622500000)
theorem polynomial_eval (lam S q : ℝ) : polynomial.eval lam S q=value lam S q := by
  norm_num [polynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,value]
  <;> ring

def box : Fin 3→RatInterval := ![⟨(41/50), (37/40)⟩, ⟨0, (1/8)⟩, ⟨0, 1⟩]
def certificate : TensorBernstein3 := [
  ⟨(55913552579407/407075840000000), 0, 2, 0, 2, 0, 0⟩,
  ⟨(2986226580657/203537920000000), 0, 2, 1, 1, 0, 0⟩,
  ⟨(5028369331907/407075840000000), 0, 2, 2, 0, 0, 0⟩,
  ⟨(119399141359951/203537920000000), 1, 1, 0, 2, 0, 0⟩,
  ⟨(104639234309277/203537920000000), 1, 1, 1, 1, 0, 0⟩,
  ⟨(10932237104519/50884480000000), 1, 1, 2, 0, 0, 0⟩,
  ⟨(39792099922499/81415168000000), 2, 0, 0, 2, 0, 0⟩,
  ⟨(11477249235687/20353792000000), 2, 0, 1, 1, 0, 0⟩,
  ⟨(18518545457749/81415168000000), 2, 0, 2, 0, 0, 0⟩]

theorem checked : certificate.boxCheck (polynomial.add [[[(-2986226580657/407075840000000)]]]) box=true := by
  decide +kernel

theorem positive (x : Fin 3→ℝ) (hx : ∀ i,(box i).Contains (x i)) :
    0<value (x 0) (x 1) (x 2) := by
  have hh := TensorBernstein3.boxCheck_sound checked x hx
  have he : RationalPolynomial3.eval [[[(-2986226580657/407075840000000)]]] (x 0) (x 1) (x 2)=
      (((-2986226580657/407075840000000):ℚ):ℝ) := by
    simp [RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval]
  rw [RationalPolynomial3.eval_add,he,polynomial_eval] at hh
  have hm : (0:ℝ)<(2986226580657/407075840000000) := by norm_num
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] at hh
  linarith only [hh,hm]

end OptimalG.Certificates.TailMonotonicityData.Corner3
