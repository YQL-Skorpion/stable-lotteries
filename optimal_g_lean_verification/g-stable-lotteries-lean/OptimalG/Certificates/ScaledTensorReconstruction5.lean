import OptimalG.Certificates.TensorBoxReconstructionHigher

/-! A positive common denominator makes Bernstein reconstruction integral.
The original polynomial and its box remain exact rational data. -/
namespace OptimalG.Certificates
open Set

namespace TensorBernstein5

def scaledBoxCheck (ts : TensorBernstein5) (p : RationalPolynomial5)
    (box : Fin 5→RatInterval) (scale : ℚ) : Bool :=
  decide (0<scale) && decide (∀ i,(box i).lo<(box i).hi) &&
    ts.reconstructCheck ((p.compose
      [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]
      [(box 3).lo,(box 3).hi-(box 3).lo]
      [(box 4).lo,(box 4).hi-(box 4).lo]).scale scale)

theorem scaledBoxCheck_sound {ts : TensorBernstein5} {p : RationalPolynomial5}
    {box : Fin 5→RatInterval} {scale : ℚ} (hc : ts.scaledBoxCheck p box scale=true)
    (x : Fin 5→ℝ) (hx : ∀ i,(box i).Contains (x i)) :
    0≤p.eval (x 0) (x 1) (x 2) (x 3) (x 4) := by
  have hh : ((0<scale) ∧ (∀ i,(box i).lo<(box i).hi)) ∧
      ts.reconstructCheck ((p.compose
        [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]
      [(box 3).lo,(box 3).hi-(box 3).lo]
      [(box 4).lo,(box 4).hi-(box 4).lo]).scale scale)=true := by
    simpa only [scaledBoxCheck,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
  have hs : (0:ℝ)<scale := by exact_mod_cast hh.1.1
  have hw (i : Fin 5) : ((box i).lo:ℝ)<(box i).hi := by exact_mod_cast hh.1.2 i
  let t : Fin 5→ℝ := fun i=>(x i-(box i).lo)/((box i).hi-(box i).lo)
  have ht (i : Fin 5) : t i∈Icc (0:ℝ) 1 := normalized_coordinate_mem (hw i) (hx i)
  have undo (i : Fin 5) :
      RationalPolynomial.eval [(box i).lo,(box i).hi-(box i).lo] (t i)=x i := by
    simp only [RationalPolynomial.eval,Rat.cast_sub,mul_zero,add_zero]
    dsimp [t]
    field_simp [(sub_pos.mpr (hw i)).ne']
    ring
  have hn := reconstructCheck_sound hh.2 (ht 0) (ht 1) (ht 2) (ht 3) (ht 4)
  rw [RationalPolynomial5.eval_scale,RationalPolynomial5.eval_compose,undo,undo,undo,undo,undo] at hn
  exact nonneg_of_mul_nonneg_right hn hs

end TensorBernstein5
end OptimalG.Certificates
