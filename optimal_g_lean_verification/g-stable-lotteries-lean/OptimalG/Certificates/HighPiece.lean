import OptimalG.Certificates.CubicConstraints

/-! Exact polynomial inequalities for an explicit high-rank subsolution. -/
namespace OptimalG.Certificates.CubicPiece

def highResidual (q : CubicPiece) (L S penalty p C alpha : ℚ) : PowerPolynomial5 :=
  let h:=q.length
  ⟨-C*(q.lo-L)+alpha*(q.f0-L*(q.lo-p)+(q.lo-p)^2/2+S)-penalty-q.a0,
   -C*h+alpha*(q.a0-L+q.lo-p)*h-q.a1*h,
   alpha*(q.a1+1)/2*h^2-q.a2*h^2,
   alpha*q.a2/3*h^3-q.a3*h^3,
   alpha*q.a3/4*h^4,0⟩

/-- The polynomial is exactly the conservative affine control minus the
proposed trajectory's derivative, not a sampled approximation. -/
theorem highResidual_eval (q : CubicPiece) (L S penalty p C alpha : ℚ) (t : ℝ) :
    (q.highResidual L S penalty p C alpha).eval t =
      -(C:ℝ)*((q.lo:ℝ)+(q.length:ℝ)*t-L)+
        (alpha:ℝ)*(q.primitive ((q.length:ℝ)*t)-
          quadratic L ((q.lo:ℝ)+(q.length:ℝ)*t-p)+S)-penalty-
        q.score ((q.length:ℝ)*t) := by
  simp only [highResidual,PowerPolynomial5.eval,primitive,score,quadratic,Rat.cast_mul,
    Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_neg,Rat.cast_pow,Rat.cast_zero,
    Rat.cast_one,Rat.cast_ofNat]
  ring

def highLineResidual (q : CubicPiece) (L : ℚ) : PowerPolynomial5 :=
  ⟨L-q.lo-q.a0,-(1+q.a1)*q.length,-q.a2*q.length^2,-q.a3*q.length^3,0,0⟩

theorem highLineResidual_eval (q : CubicPiece) (L : ℚ) (t : ℝ) :
    (q.highLineResidual L).eval t=(L:ℝ)-((q.lo:ℝ)+(q.length:ℝ)*t)-q.score ((q.length:ℝ)*t) := by
  exact ceilingPolynomial_eval q L t

/-- The full closed step interval satisfies the checked differential inequality. -/
theorem highResidual_sound {q : CubicPiece} {L S penalty p C alpha : ℚ}
    (hlen : 0<q.length) (hc : (q.highResidual L S penalty p C alpha).nonnegativeCheck=true)
    {z : ℝ} (hz : z∈Set.Icc (q.lo:ℝ) (q.hi:ℝ)) :
    q.score (z-q.lo)≤-(C:ℝ)*(z-L)+(alpha:ℝ)*(q.primitive (z-q.lo)-quadratic L (z-p)+S)-penalty := by
  have hl : (0:ℝ)<q.length := by exact_mod_cast hlen
  let t : ℝ := (z-q.lo)/q.length
  have ht : t∈Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hz.1) hl.le
    · apply (div_le_iff₀ hl).mpr
      norm_num [length]
      linarith [hz.2]
  have hlt : (q.length:ℝ)*t=z-q.lo := by dsimp [t]; field_simp
  have he : (q.lo:ℝ)+(q.length:ℝ)*t=z := by rw [hlt]; ring
  have hb := PowerPolynomial5.nonnegativeCheck_sound hc ht
  rw [highResidual_eval,he,hlt] at hb
  linarith

end OptimalG.Certificates.CubicPiece
