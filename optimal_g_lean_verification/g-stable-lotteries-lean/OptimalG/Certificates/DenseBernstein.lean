import OptimalG.Certificates.TensorBoxReconstruction

/-! Separable Bernstein-Horner reconstruction. Natural coefficients make
positivity structural; the only computed assertion is polynomial equality.
An axis is reconstructed as b*(1-x)^n+x*(remaining axis). -/
namespace OptimalG.Certificates
open Set

abbrev DenseBernstein1 := List ℕ
namespace DenseBernstein1

def polynomial : DenseBernstein1→RationalPolynomial
  | []=>[]
  | b::bs=>RationalPolynomial.add
      (RationalPolynomial.scale (b:ℚ) (RationalPolynomial.pow [1,-1] bs.length))
      (0::polynomial bs)

theorem polynomial_nonneg (bs : DenseBernstein1) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    0≤bs.polynomial.eval x := by
  induction bs with
  | nil=>simp [polynomial,RationalPolynomial.eval]
  | cons b bs ih=>
    have hp := pow_nonneg (sub_nonneg.mpr hx.2) bs.length
    have h1 := mul_nonneg (Nat.cast_nonneg b : (0:ℝ)≤b) hp
    have h2 := mul_nonneg hx.1 ih
    have he : RationalPolynomial.eval [1,-1] x=1-x := by simp [RationalPolynomial.eval, sub_eq_add_neg]
    simpa only [polynomial,RationalPolynomial.eval_add,RationalPolynomial.eval_scale,
      RationalPolynomial.eval_pow,he,RationalPolynomial.eval,Rat.cast_natCast,Rat.cast_zero,Rat.cast_one,Rat.cast_neg,
      zero_add,mul_zero,add_zero,mul_one,mul_neg,sub_eq_add_neg] using add_nonneg h1 h2

end DenseBernstein1

abbrev DenseBernstein2 := List DenseBernstein1
namespace DenseBernstein2

def polynomial : DenseBernstein2→RationalPolynomial2
  | []=>[]
  | b::bs=>RationalPolynomial2.add
      (RationalPolynomial2.mulFirst (RationalPolynomial.pow [1,-1] bs.length)
        [DenseBernstein1.polynomial b])
      ([]::polynomial bs)

theorem polynomial_nonneg (bs : DenseBernstein2) {x y : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    0≤bs.polynomial.eval x y := by
  induction bs with
  | nil=>simp [polynomial,RationalPolynomial2.eval]
  | cons b bs ih=>
    have hp := pow_nonneg (sub_nonneg.mpr hx.2) bs.length
    have h1 := mul_nonneg hp (DenseBernstein1.polynomial_nonneg b hy)
    have h2 := mul_nonneg hx.1 ih
    have he : RationalPolynomial.eval [1,-1] x=1-x := by simp [RationalPolynomial.eval, sub_eq_add_neg]
    simpa only [polynomial,RationalPolynomial2.eval_add,RationalPolynomial2.eval_mulFirst,
      RationalPolynomial.eval_pow,he,RationalPolynomial2.eval,RationalPolynomial.eval,
      Rat.cast_zero,Rat.cast_one,Rat.cast_neg,mul_zero,add_zero,zero_add,mul_one,mul_neg,
      sub_eq_add_neg] using add_nonneg h1 h2

end DenseBernstein2

abbrev DenseBernstein3 := List DenseBernstein2
namespace DenseBernstein3

def polynomial : DenseBernstein3→RationalPolynomial3
  | []=>[]
  | b::bs=>RationalPolynomial3.add
      (RationalPolynomial3.mulFirst (RationalPolynomial.pow [1,-1] bs.length)
        [DenseBernstein2.polynomial b])
      ([]::polynomial bs)

theorem polynomial_nonneg (bs : DenseBernstein3) {x y z : ℝ}
    (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) :
    0≤bs.polynomial.eval x y z := by
  induction bs with
  | nil=>simp [polynomial,RationalPolynomial3.eval]
  | cons b bs ih=>
    have hp := pow_nonneg (sub_nonneg.mpr hx.2) bs.length
    have h1 := mul_nonneg hp (DenseBernstein2.polynomial_nonneg b hy hz)
    have h2 := mul_nonneg hx.1 ih
    have he : RationalPolynomial.eval [1,-1] x=1-x := by simp [RationalPolynomial.eval, sub_eq_add_neg]
    simpa only [polynomial,RationalPolynomial3.eval_add,RationalPolynomial3.eval_mulFirst,
      RationalPolynomial.eval_pow,he,RationalPolynomial3.eval,RationalPolynomial2.eval,
      Rat.cast_zero,Rat.cast_one,Rat.cast_neg,mul_zero,add_zero,zero_add,mul_one,mul_neg,
      sub_eq_add_neg] using add_nonneg h1 h2

def scaledBoxCheck (bs : DenseBernstein3) (scale : ℚ) (p : RationalPolynomial3)
    (box : Fin 3→RatInterval) : Bool :=
  decide (0<scale) && (decide (∀ i,(box i).lo<(box i).hi) &&
    ((p.scale scale).compose [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]).eqCheck bs.polynomial)

theorem scaledBoxCheck_sound {bs : DenseBernstein3} {scale : ℚ}
    {p : RationalPolynomial3} {box : Fin 3→RatInterval}
    (hc : bs.scaledBoxCheck scale p box=true) (x : Fin 3→ℝ)
    (hx : ∀ i,(box i).Contains (x i)) : 0≤p.eval (x 0) (x 1) (x 2) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hs : (0:ℚ)<scale := of_decide_eq_true hh.1
  have hs' : (0:ℝ)<(scale:ℝ) := by exact_mod_cast hs
  have hh' := Bool.and_eq_true_iff.mp hh.2
  have hwq : ∀ i,(box i).lo<(box i).hi := of_decide_eq_true hh'.1
  have hw (i : Fin 3) : ((box i).lo:ℝ)<(box i).hi := by exact_mod_cast hwq i
  let t : Fin 3→ℝ := fun i=>(x i-(box i).lo)/((box i).hi-(box i).lo)
  have ht (i : Fin 3) : t i∈Icc (0:ℝ) 1 := normalized_coordinate_mem (hw i) (hx i)
  have undo (i : Fin 3) :
      RationalPolynomial.eval [(box i).lo,(box i).hi-(box i).lo] (t i)=x i := by
    simp only [RationalPolynomial.eval,Rat.cast_sub,mul_zero,add_zero]
    dsimp [t]
    field_simp [(sub_pos.mpr (hw i)).ne']
    ring
  have he := RationalPolynomial3.eqCheck_sound hh'.2 (t 0) (t 1) (t 2)
  have hn : 0≤((p.scale scale).compose [(box 0).lo,(box 0).hi-(box 0).lo]
      [(box 1).lo,(box 1).hi-(box 1).lo]
      [(box 2).lo,(box 2).hi-(box 2).lo]).eval (t 0) (t 1) (t 2) := by
    rw [he]
    exact polynomial_nonneg bs (ht 0) (ht 1) (ht 2)
  rw [RationalPolynomial3.eval_compose,undo,undo,undo,RationalPolynomial3.eval_scale] at hn
  exact nonneg_of_mul_nonneg_right hn hs'

end DenseBernstein3
end OptimalG.Certificates
