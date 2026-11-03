import OptimalG.Certificates.CubicAssembly
import OptimalG.Certificates.Bernstein5
import OptimalG.Certificates.Slater

/-! Full-interval score, ceiling, and primitive-cap checks for each cubic piece. -/

namespace OptimalG.Certificates.CubicPiece

def scorePolynomial (p : CubicPiece) : PowerPolynomial5 :=
  ⟨p.a0,p.a1*p.length,p.a2*p.length^2,p.a3*p.length^3,0,0⟩

def ceilingPolynomial (p : CubicPiece) (L : ℚ) : PowerPolynomial5 :=
  ⟨L-p.lo-p.a0,-(1+p.a1)*p.length,-p.a2*p.length^2,-p.a3*p.length^3,0,0⟩

def capPolynomial (p : CubicPiece) (L S : ℚ) : PowerPolynomial5 :=
  let d := 1-p.lo
  let c0 := L^2-L/2+L*p.lo/2-p.f0
  let c1 := (L/2-p.a0)*p.length
  let c2 := -p.a1/2*p.length^2
  let c3 := -p.a2/3*p.length^3
  let c4 := -p.a3/4*p.length^4
  ⟨d*c0-L*S,d*c1-p.length*c0,d*c2-p.length*c1,d*c3-p.length*c2,
    d*c4-p.length*c3,-p.length*c4⟩

theorem scorePolynomial_eval (p : CubicPiece) (t : ℝ) :
    p.scorePolynomial.eval t=p.score ((p.length:ℝ)*t) := by
  simp only [scorePolynomial,PowerPolynomial5.eval,score,Rat.cast_zero,Rat.cast_mul,Rat.cast_pow]
  ring

theorem ceilingPolynomial_eval (p : CubicPiece) (L : ℚ) (t : ℝ) :
    (p.ceilingPolynomial L).eval t=(L:ℝ)-(p.lo+(p.length:ℝ)*t)-p.score ((p.length:ℝ)*t) := by
  simp only [ceilingPolynomial,PowerPolynomial5.eval,score,Rat.cast_zero,Rat.cast_mul,
    Rat.cast_pow,Rat.cast_sub,Rat.cast_add,Rat.cast_neg,Rat.cast_one]
  ring

theorem capPolynomial_eval (p : CubicPiece) (L S : ℚ) (t : ℝ) :
    (p.capPolynomial L S).eval t =
      (1-((p.lo:ℝ)+(p.length:ℝ)*t))*
        ((L:ℝ)^2-(L:ℝ)/2+(L:ℝ)*((p.lo:ℝ)+(p.length:ℝ)*t)/2-
          p.primitive ((p.length:ℝ)*t))-(L:ℝ)*S := by
  simp only [capPolynomial,PowerPolynomial5.eval,primitive,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_sub,Rat.cast_add,Rat.cast_neg,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
  ring

def feasibleCheck (p : CubicPiece) (L S : ℚ) : Bool :=
  decide (p.lo<p.hi ∧ p.hi<1) &&
    (p.scorePolynomial.nonnegativeCheck &&
      ((p.ceilingPolynomial L).nonnegativeCheck && (p.capPolynomial L S).nonnegativeCheck))

/-- Every point of the closed piece interval satisfies all three constraints.
The proof permits exact contact at either endpoint. -/
theorem feasibleCheck_sound {p : CubicPiece} {L S : ℚ} (hc : p.feasibleCheck L S=true)
    {r : ℝ} (hr : r ∈ Set.Icc (p.lo:ℝ) (p.hi:ℝ)) :
    0≤p.score (r-p.lo) ∧ p.score (r-p.lo)≤(L:ℝ)-r ∧
      p.primitive (r-p.lo)≤cap L S r := by
  have hchecks : (p.lo<p.hi ∧ p.hi<1) ∧ p.scorePolynomial.nonnegativeCheck=true ∧
      (p.ceilingPolynomial L).nonnegativeCheck=true ∧ (p.capPolynomial L S).nonnegativeCheck=true := by
    simpa only [feasibleCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  have hlen : (0:ℝ)<p.length := by
    have hh : (0:ℚ)<p.length := sub_pos.mpr hchecks.1.1
    exact_mod_cast hh
  let t : ℝ := (r-p.lo)/p.length
  have ht : t ∈ Set.Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hr.1) (le_of_lt hlen)
    · apply (div_le_iff₀ hlen).mpr
      norm_num [length]
      linarith [hr.2]
  have hlt : (p.length:ℝ)*t=r-p.lo := by
    dsimp [t]
    field_simp
  have hr' : (p.lo:ℝ)+(p.length:ℝ)*t=r := by rw [hlt]; ring
  have hs := PowerPolynomial5.nonnegativeCheck_sound hchecks.2.1 ht
  have hl := PowerPolynomial5.nonnegativeCheck_sound hchecks.2.2.1 ht
  have hp := PowerPolynomial5.nonnegativeCheck_sound hchecks.2.2.2 ht
  rw [scorePolynomial_eval,hlt] at hs
  rw [ceilingPolynomial_eval,hr',hlt] at hl
  rw [capPolynomial_eval,hr',hlt] at hp
  have hhi : (p.hi:ℝ)<1 := by exact_mod_cast hchecks.1.2
  have hd : 0<1-r := by linarith [hr.2]
  have hcap : (1-r)*(cap (L:ℝ) (S:ℝ) r-p.primitive (r-p.lo)) =
      (1-r)*((L:ℝ)^2-(L:ℝ)/2+(L:ℝ)*r/2-p.primitive (r-p.lo))-(L:ℝ)*S := by
    unfold cap
    field_simp
    ring
  rw [← hcap] at hp
  have hgap := (mul_nonneg_iff_of_pos_left hd).mp hp
  exact ⟨hs,by linarith,by linarith⟩

end OptimalG.Certificates.CubicPiece
