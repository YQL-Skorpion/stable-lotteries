import OptimalG.Certificates.TensorBoxReconstruction

namespace OptimalG.Certificates.TailMonotonicityData.Corner1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def polynomial : RationalPolynomial3 := [[[(142826755763/1183360000000)], [(-42990672423/81415168000)]], [[(-35353518401/11833600000)], [(6315928861/814151680)], [(118273125/10176896)]], [[(865369/236672)], [(-118273125/10176896)]]]
noncomputable def value (lam S q : ℝ) : ℝ :=
  (-118273125/10176896)*lam^2*S
    + (865369/236672)*lam^2
    + (118273125/10176896)*lam*S^2
    + (6315928861/814151680)*lam*S
    + (-35353518401/11833600000)*lam
    + (-42990672423/81415168000)*S
    + (142826755763/1183360000000)
theorem polynomial_eval (lam S q : ℝ) : polynomial.eval lam S q=value lam S q := by
  norm_num [polynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,value]
  <;> ring

def box : Fin 3→RatInterval := ![⟨(41/50), (37/40)⟩, ⟨0, (1/8)⟩, ⟨0, 1⟩]
def certificate : TensorBernstein3 := [
  ⟨(206219733906253/1628303360000000), 0, 2, 0, 2, 0, 0⟩,
  ⟨(4595609130003/814151680000000), 0, 2, 1, 1, 0, 0⟩,
  ⟨(45431390603753/1628303360000000), 0, 2, 2, 0, 0, 0⟩,
  ⟨(463442820769429/814151680000000), 1, 1, 0, 2, 0, 0⟩,
  ⟨(402867637036983/814151680000000), 1, 1, 1, 1, 0, 0⟩,
  ⟨(49352017543451/203537920000000), 1, 1, 2, 0, 0, 0⟩,
  ⟨(157261175404121/325660672000000), 2, 0, 0, 2, 0, 0⟩,
  ⟨(45087238526373/81415168000000), 2, 0, 1, 1, 0, 0⟩,
  ⟨(77789099013871/325660672000000), 2, 0, 2, 0, 0, 0⟩]

theorem checked : certificate.boxCheck (polynomial.add [[[(-4595609130003/1628303360000000)]]]) box=true := by
  decide +kernel

theorem positive (x : Fin 3→ℝ) (hx : ∀ i,(box i).Contains (x i)) :
    0<value (x 0) (x 1) (x 2) := by
  have hh := TensorBernstein3.boxCheck_sound checked x hx
  have he : RationalPolynomial3.eval [[[(-4595609130003/1628303360000000)]]] (x 0) (x 1) (x 2)=
      (((-4595609130003/1628303360000000):ℚ):ℝ) := by
    simp [RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval]
  rw [RationalPolynomial3.eval_add,he,polynomial_eval] at hh
  have hm : (0:ℝ)<(4595609130003/1628303360000000) := by norm_num
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] at hh
  linarith only [hh,hm]

end OptimalG.Certificates.TailMonotonicityData.Corner1
