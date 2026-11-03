import OptimalG.Certificates.TensorBoxReconstruction

namespace OptimalG.Certificates.TailMonotonicityData.Corner0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def polynomial : RationalPolynomial3 := [[[(145757364863/1183360000000)], [(-47386586073/81415168000)]], [[(-36078924101/11833600000)], [(7315285411/814151680)], [(130366875/10176896)]], [[(878269/236672)], [(-130366875/10176896)]]]
noncomputable def value (lam S q : ℝ) : ℝ :=
  (-130366875/10176896)*lam^2*S
    + (878269/236672)*lam^2
    + (130366875/10176896)*lam*S^2
    + (7315285411/814151680)*lam*S
    + (-36078924101/11833600000)*lam
    + (-47386586073/81415168000)*S
    + (145757364863/1183360000000)
theorem polynomial_eval (lam S q : ℝ) : polynomial.eval lam S q=value lam S q := by
  norm_num [polynomial,RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval,value]
  <;> ring

def box : Fin 3→RatInterval := ![⟨(41/50), (37/40)⟩, ⟨0, (1/8)⟩, ⟨0, 1⟩]
def certificate : TensorBernstein3 := [
  ⟨(189339537739603/1628303360000000), 0, 2, 0, 2, 0, 0⟩,
  ⟨(3336192275853/814151680000000), 0, 2, 1, 1, 0, 0⟩,
  ⟨(84584940562103/1628303360000000), 0, 2, 2, 0, 0, 0⟩,
  ⟨(448963841025979/814151680000000), 1, 1, 0, 2, 0, 0⟩,
  ⟨(397442353393833/814151680000000), 1, 1, 1, 1, 0, 0⟩,
  ⟨(58210314615401/203537920000000), 1, 1, 2, 0, 0, 0⟩,
  ⟨(155041320900071/325660672000000), 2, 0, 0, 2, 0, 0⟩,
  ⟨(44635167333723/81415168000000), 2, 0, 1, 1, 0, 0⟩,
  ⟨(83794028122321/325660672000000), 2, 0, 2, 0, 0, 0⟩]

theorem checked : certificate.boxCheck (polynomial.add [[[(-3336192275853/1628303360000000)]]]) box=true := by
  decide +kernel

theorem positive (x : Fin 3→ℝ) (hx : ∀ i,(box i).Contains (x i)) :
    0<value (x 0) (x 1) (x 2) := by
  have hh := TensorBernstein3.boxCheck_sound checked x hx
  have he : RationalPolynomial3.eval [[[(-3336192275853/1628303360000000)]]] (x 0) (x 1) (x 2)=
      (((-3336192275853/1628303360000000):ℚ):ℝ) := by
    simp [RationalPolynomial3.eval,RationalPolynomial2.eval,RationalPolynomial.eval]
  rw [RationalPolynomial3.eval_add,he,polynomial_eval] at hh
  have hm : (0:ℝ)<(3336192275853/1628303360000000) := by norm_num
  norm_num only [Rat.cast_neg,Rat.cast_div,Rat.cast_natCast,Rat.cast_intCast] at hh
  linarith only [hh,hm]

end OptimalG.Certificates.TailMonotonicityData.Corner0
