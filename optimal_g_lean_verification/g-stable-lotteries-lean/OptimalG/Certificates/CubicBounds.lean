import OptimalG.Certificates.CubicConstraints

/-! A recursive certificate covering all cubic pieces and the final quadratic tail. -/

namespace OptimalG.Certificates

open Set

def quadraticTail (L S a b : ℚ) : CubicPiece :=
  ⟨a,b,L-a,-1,0,0,L*a-a^2/2-S⟩

theorem quadraticTail_score (L S a b : ℚ) (r : ℝ) :
    (quadraticTail L S a b).score (r-a)=(L:ℝ)-r := by
  simp only [quadraticTail,CubicPiece.score,Rat.cast_sub,Rat.cast_neg,Rat.cast_one,Rat.cast_zero]
  ring

theorem quadraticTail_primitive (L S a b : ℚ) (r : ℝ) :
    (quadraticTail L S a b).primitive (r-a)=(L:ℝ)*r-r^2/2-S := by
  simp only [quadraticTail,CubicPiece.primitive,Rat.cast_sub,Rat.cast_neg,Rat.cast_one,
    Rat.cast_zero,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_ofNat]
  ring

def cubicBoundsCheck (L S b : ℚ) : ℚ → List CubicPiece → Bool
  | a, [] => (quadraticTail L S a b).feasibleCheck L S
  | a, p::ps => decide (p.lo=a) && (p.feasibleCheck L S && cubicBoundsCheck L S b p.hi ps)

/-- The verified partition covers every real rank, including every join. -/
theorem cubicBoundsCheck_sound {L S b a : ℚ} {ps : List CubicPiece}
    (hc : cubicBoundsCheck L S b a ps=true) {r : ℝ} (hr : r∈Icc (a:ℝ) (b:ℝ)) :
    0≤cubicScore L ps r ∧ cubicScore L ps r≤(L:ℝ)-r ∧
      cubicPrimitive L S ps r≤cap L S r := by
  induction ps generalizing a with
  | nil =>
    have hb := CubicPiece.feasibleCheck_sound hc hr
    change 0≤(quadraticTail L S a b).score (r-a) ∧
      (quadraticTail L S a b).score (r-a)≤(L:ℝ)-r ∧
      (quadraticTail L S a b).primitive (r-a)≤cap L S r at hb
    simpa only [quadraticTail_score,quadraticTail_primitive,cubicScore,cubicPrimitive] using hb
  | cons p ps ih =>
    have hh : p.lo=a ∧ p.feasibleCheck L S=true ∧ cubicBoundsCheck L S b p.hi ps=true := by
      simpa only [cubicBoundsCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    by_cases hp : r≤p.hi
    · have hb := CubicPiece.feasibleCheck_sound hh.2.1 ⟨by simpa [hh.1] using hr.1,hp⟩
      simpa only [cubicScore,cubicPrimitive,if_pos hp] using hb
    · have hb := ih hh.2.2 ⟨le_of_lt (lt_of_not_ge hp),hr.2⟩
      simpa only [cubicScore,cubicPrimitive,if_neg hp] using hb

end OptimalG.Certificates
