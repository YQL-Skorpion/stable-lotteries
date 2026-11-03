import OptimalG.Certificates.TensorBoxReconstruction

/-! A positive common scale makes every Bernstein coefficient integral while
retaining exact reconstruction of the original rational polynomial. -/
namespace OptimalG.Certificates.TensorBernstein3
open Set

def scaledBoxCheck (ts : TensorBernstein3) (scale : ℚ) (p : RationalPolynomial3)
    (box : Fin 3→RatInterval) : Bool :=
  decide (0<scale) && ts.boxCheck (p.scale scale) box

theorem scaledBoxCheck_sound {ts : TensorBernstein3} {scale : ℚ}
    {p : RationalPolynomial3} {box : Fin 3→RatInterval}
    (hc : ts.scaledBoxCheck scale p box=true) (x : Fin 3→ℝ)
    (hx : ∀ i,(box i).Contains (x i)) : 0≤p.eval (x 0) (x 1) (x 2) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hs : 0<scale := of_decide_eq_true hh.1
  have hs' : (0:ℝ)<(scale:ℝ) := by exact_mod_cast hs
  have hp := boxCheck_sound hh.2 x hx
  rw [RationalPolynomial3.eval_scale] at hp
  exact nonneg_of_mul_nonneg_right hp hs'

end OptimalG.Certificates.TensorBernstein3
