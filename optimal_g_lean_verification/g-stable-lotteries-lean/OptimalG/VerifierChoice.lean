import OptimalG.ThreeFunctionTest

/-! Pointwise sufficient coefficients need no regularity in lottery mass.
Classical choice joins independently verified masses into one verifier. -/
namespace OptimalG
open Set

theorem VerifierOn.of_singletons {M : Set ℝ} {phi : ℝ→ℝ} {lam : ℝ}
    {beta : ℝ→ℝ} {corr : ℝ→ℝ→ℝ}
    (h : ∀ p∈M,VerifierOn {p} phi lam (fun _=>beta p) (fun _=>corr p)) :
    VerifierOn M phi lam beta corr := by
  constructor
  · intro p hp; exact (h p hp).beta_nonneg p rfl
  · intro p hp; exact (h p hp).corr_nonneg p rfl
  · intro p hp; exact (h p hp).low_first p rfl
  · intro p hp; exact (h p hp).low_second p rfl
  · intro p hp; exact (h p hp).high_first p rfl
  · intro p hp; exact (h p hp).high_second p rfl

theorem exists_verifier_of_singletons {M : Set ℝ} {phi : ℝ→ℝ} {lam : ℝ}
    (h : ∀ p∈M,∃ b : ℝ,∃ c : ℝ→ℝ,
      VerifierOn {p} phi lam (fun _=>b) (fun _=>c)) :
    ∃ beta corr,VerifierOn M phi lam beta corr := by
  classical
  have hall : ∀ p,∃ b : ℝ,∃ c : ℝ→ℝ,
      p∈M→VerifierOn {p} phi lam (fun _=>b) (fun _=>c) := by
    intro p
    by_cases hp : p∈M
    · obtain ⟨b,c,hbc⟩ := h p hp
      exact ⟨b,c,fun _=>hbc⟩
    · exact ⟨0,fun _=>0,fun hm=>False.elim (hp hm)⟩
  choose beta corr hc using hall
  exact ⟨beta,corr,VerifierOn.of_singletons hc⟩

end OptimalG
