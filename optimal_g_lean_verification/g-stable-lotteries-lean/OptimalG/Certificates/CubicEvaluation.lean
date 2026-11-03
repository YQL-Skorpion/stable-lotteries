import OptimalG.Certificates.CubicAssembly

namespace OptimalG.Certificates

theorem cubicScore_at_first (L : ℝ) (p : CubicPiece) (ps : List CubicPiece)
    (hh : p.lo≤p.hi) : cubicScore L (p::ps) p.lo=p.a0 := by
  have hh' : (p.lo:ℝ)≤p.hi := by exact_mod_cast hh
  rw [cubicScore,if_pos hh']
  simp [CubicPiece.score]

theorem cubicPrimitive_at_first (L S : ℝ) (p : CubicPiece) (ps : List CubicPiece)
    (hh : p.lo≤p.hi) : cubicPrimitive L S (p::ps) p.lo=p.f0 := by
  have hh' : (p.lo:ℝ)≤p.hi := by exact_mod_cast hh
  rw [cubicPrimitive,if_pos hh']
  simp [CubicPiece.primitive]

theorem cubic_tail_values (L S r : ℝ) (ps : List CubicPiece)
    (hh : ∀ p∈ps, (p.hi:ℝ)<r) :
    cubicScore L ps r=L-r ∧ cubicPrimitive L S ps r=L*r-r^2/2-S := by
  induction ps with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    have hp : ¬r≤p.hi := not_le_of_gt (hh p (List.mem_cons_self))
    have ht := ih (fun q hq => hh q (List.mem_cons_of_mem p hq))
    simpa only [cubicScore,cubicPrimitive,if_neg hp] using ht

end OptimalG.Certificates
