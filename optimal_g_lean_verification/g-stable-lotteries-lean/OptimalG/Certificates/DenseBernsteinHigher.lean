import OptimalG.Certificates.DenseBernstein
import OptimalG.Certificates.TensorReconstructionHigher

/-! Four- and five-coordinate separable Bernstein-Horner certificates.
Natural coefficient positivity is structural; only exact coefficient
identities and positive scales are checked computationally. -/
namespace OptimalG.Certificates
open Set

abbrev DenseBernstein4 := List DenseBernstein3
namespace DenseBernstein4

def polynomial : DenseBernstein4 → RationalPolynomial4
  | [] => []
  | b::bs => RationalPolynomial4.add
      (RationalPolynomial4.mulFirst (RationalPolynomial.pow [1,-1] bs.length)
        [DenseBernstein3.polynomial b])
      ([]::polynomial bs)

theorem polynomial_nonneg (bs : DenseBernstein4) {u v w x : ℝ}
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (hw : w∈Icc (0:ℝ) 1) (hx : x∈Icc (0:ℝ) 1) :
    0≤bs.polynomial.eval u v w x := by
  induction bs with
  | nil => simp [polynomial,RationalPolynomial4.eval]
  | cons b bs ih =>
    have hp := pow_nonneg (sub_nonneg.mpr hu.2) bs.length
    have h1 := mul_nonneg hp (DenseBernstein3.polynomial_nonneg b hv hw hx)
    have h2 := mul_nonneg hu.1 ih
    have he : RationalPolynomial.eval [1,-1] u=1-u := by
      simp [RationalPolynomial.eval, sub_eq_add_neg]
    simpa only [polynomial,RationalPolynomial4.eval_add,RationalPolynomial4.eval_mulFirst,
      RationalPolynomial.eval_pow,he,RationalPolynomial4.eval,RationalPolynomial3.eval,
      Rat.cast_zero,Rat.cast_one,Rat.cast_neg,mul_zero,add_zero,zero_add,mul_one,mul_neg,
      sub_eq_add_neg] using add_nonneg h1 h2

end DenseBernstein4

abbrev DenseBernstein5 := List DenseBernstein4
namespace DenseBernstein5

def polynomial : DenseBernstein5 → RationalPolynomial5
  | [] => []
  | b::bs => RationalPolynomial5.add
      (RationalPolynomial5.mulFirst (RationalPolynomial.pow [1,-1] bs.length)
        [DenseBernstein4.polynomial b])
      ([]::polynomial bs)

theorem polynomial_nonneg (bs : DenseBernstein5) {u v w x y : ℝ}
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (hw : w∈Icc (0:ℝ) 1) (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    0≤bs.polynomial.eval u v w x y := by
  induction bs with
  | nil => simp [polynomial,RationalPolynomial5.eval]
  | cons b bs ih =>
    have hp := pow_nonneg (sub_nonneg.mpr hu.2) bs.length
    have h1 := mul_nonneg hp (DenseBernstein4.polynomial_nonneg b hv hw hx hy)
    have h2 := mul_nonneg hu.1 ih
    have he : RationalPolynomial.eval [1,-1] u=1-u := by
      simp [RationalPolynomial.eval, sub_eq_add_neg]
    simpa only [polynomial,RationalPolynomial5.eval_add,RationalPolynomial5.eval_mulFirst,
      RationalPolynomial.eval_pow,he,RationalPolynomial5.eval,RationalPolynomial4.eval,
      Rat.cast_zero,Rat.cast_one,Rat.cast_neg,mul_zero,add_zero,zero_add,mul_one,mul_neg,
      sub_eq_add_neg] using add_nonneg h1 h2

def scaledBoxCheck (bs : DenseBernstein5) (scale : ℚ) (p : RationalPolynomial5)
    (box : Fin 5→RatInterval) : Bool :=
  decide (0<scale) && (decide (∀ i,(box i).lo<(box i).hi) &&
    ((p.scale scale).compose [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]
      [(box 3).lo,(box 3).hi-(box 3).lo]
      [(box 4).lo,(box 4).hi-(box 4).lo]).eqCheck bs.polynomial)

theorem scaledBoxCheck_sound {bs : DenseBernstein5} {scale : ℚ}
    {p : RationalPolynomial5} {box : Fin 5→RatInterval}
    (hc : bs.scaledBoxCheck scale p box=true) (x : Fin 5→ℝ)
    (hx : ∀ i,(box i).Contains (x i)) : 0≤p.eval (x 0) (x 1) (x 2) (x 3) (x 4) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hs : (0:ℚ)<scale := of_decide_eq_true hh.1
  have hs' : (0:ℝ)<(scale:ℝ) := by exact_mod_cast hs
  have hh' := Bool.and_eq_true_iff.mp hh.2
  have hwq : ∀ i,(box i).lo<(box i).hi := of_decide_eq_true hh'.1
  have hw (i : Fin 5) : ((box i).lo:ℝ)<(box i).hi := by exact_mod_cast hwq i
  let t : Fin 5→ℝ := fun i=>(x i-(box i).lo)/((box i).hi-(box i).lo)
  have ht (i : Fin 5) : t i∈Icc (0:ℝ) 1 := normalized_coordinate_mem (hw i) (hx i)
  have undo (i : Fin 5) :
      RationalPolynomial.eval [(box i).lo,(box i).hi-(box i).lo] (t i)=x i := by
    simp only [RationalPolynomial.eval,Rat.cast_sub,mul_zero,add_zero]
    dsimp [t]
    field_simp [(sub_pos.mpr (hw i)).ne']
    ring
  have he := RationalPolynomial5.eqCheck_sound hh'.2 (t 0) (t 1) (t 2) (t 3) (t 4)
  have hn : 0≤((p.scale scale).compose [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]
      [(box 3).lo,(box 3).hi-(box 3).lo]
      [(box 4).lo,(box 4).hi-(box 4).lo]).eval (t 0) (t 1) (t 2) (t 3) (t 4) := by
    rw [he]
    exact polynomial_nonneg bs (ht 0) (ht 1) (ht 2) (ht 3) (ht 4)
  rw [RationalPolynomial5.eval_compose,undo,undo,undo,undo,undo,RationalPolynomial5.eval_scale] at hn
  exact nonneg_of_mul_nonneg_right hn hs'

end DenseBernstein5
end OptimalG.Certificates
