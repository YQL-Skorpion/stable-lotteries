import OptimalG.Certificates.TensorBoxReconstruction

namespace OptimalG.Certificates.TailMonotonicityData.Corner2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def polynomial : RationalPolynomial3 := [[[(35438333747/295840000000)], [(-21691278099/40707584000)]], [[(-8771954369/2958400000)], [(3222719393/407075840)], [(59675625/5088448)]], [[(215161/59168)], [(-59675625/5088448)]]]
noncomputable def value (lam S q : ℝ) : ℝ :=
  (-59675625/5088448)*lam^2*S
    + (215161/59168)*lam^2
    + (59675625/5088448)*lam*S^2
    + (3222719393/407075840)*lam*S
    + (-8771954369/2958400000)*lam
    + (-21691278099/40707584000)*S
    + (35438333747/295840000000)
theorem polynomial_eval (lam S q : ℝ) : polynomial.eval lam S q=value lam S q := by
  norm_num [polynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,value]
  <;> ring

def box : Fin 3→RatInterval := ![⟨(41/50), (37/40)⟩, ⟨0, (1/8)⟩, ⟨0, 1⟩]
def certificate : TensorBernstein3 := [
  ⟨(103387007075489/814151680000000), 0, 2, 0, 2, 0, 0⟩,
  ⟨(5342744734239/407075840000000), 0, 2, 1, 1, 0, 0⟩,
  ⟨(29633513642989/814151680000000), 0, 2, 2, 0, 0, 0⟩,
  ⟨(231558792848177/407075840000000), 1, 1, 0, 2, 0, 0⟩,
  ⟨(206565826796979/407075840000000), 1, 1, 1, 1, 0, 0⟩,
  ⟨(26293622745013/101768960000000), 1, 1, 2, 0, 0, 0⟩,
  ⟨(78474272592973/162830336000000), 2, 0, 0, 2, 0, 0⟩,
  ⟨(22728462875049/40707584000000), 2, 0, 1, 1, 0, 0⟩,
  ⟨(40039555469723/162830336000000), 2, 0, 2, 0, 0, 0⟩]

theorem checked : certificate.boxCheck (polynomial.add [[[(-5342744734239/814151680000000)]]]) box=true := by
  decide +kernel

theorem positive (x : Fin 3→ℝ) (hx : ∀ i,(box i).Contains (x i)) :
    0<value (x 0) (x 1) (x 2) := by
  have hh := TensorBernstein3.boxCheck_sound checked x hx
  have he : RationalPolynomial3.eval [[[(-5342744734239/814151680000000)]]] (x 0) (x 1) (x 2)=
      (((-5342744734239/814151680000000):ℚ):ℝ) := by
    simp [RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval]
  rw [RationalPolynomial3.eval_add,he,polynomial_eval] at hh
  have hm : (0:ℝ)<(5342744734239/814151680000000) := by norm_num
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] at hh
  linarith only [hh,hm]

end OptimalG.Certificates.TailMonotonicityData.Corner2
