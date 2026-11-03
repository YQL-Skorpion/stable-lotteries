import OptimalG.Certificates.Compact

/-! The exact calibrated binary-constraint gains in the first relocation phase. -/
namespace OptimalG
open Set

theorem first_phase_binary_gains {lam p mu : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hp : p ∈ Icc (0.25 : ℝ) 0.38) (hmu : 0 ≤ mu) :
    0 ≤ lam*(2.98*mu+mu)-(1-p)*(2.98*mu) ∧
    0 ≤ lam*(2.98*mu)-p*(2.98*mu+mu) := by
  have hc : 0 ≤ lam*3.98-(1-p)*2.98 := by linarith [hL.1,hp.1]
  have hc' : 0 ≤ lam*2.98-p*3.98 := by linarith [hL.1,hp.2]
  have hm := mul_nonneg hc hmu
  have hm' := mul_nonneg hc' hmu
  constructor <;> nlinarith only [hm,hm']

theorem first_phase_preserves_binary {lam p mu R P t : ℝ}
    (hL : Certificates.Compact.LambdaRange lam)
    (hp : p ∈ Icc (0.25 : ℝ) 0.38) (hmu : 0 ≤ mu) (ht : 0 ≤ t)
    (hcomp : (1-p)*R ≤ lam*P) (hopp : p*P ≤ lam*R) :
    (1-p)*(R+t*(2.98*mu)) ≤ lam*(P+t*(2.98*mu+mu)) ∧
    p*(P+t*(2.98*mu+mu)) ≤ lam*(R+t*(2.98*mu)) := by
  obtain ⟨hg,hg'⟩ := first_phase_binary_gains hL hp hmu
  have hm := mul_nonneg ht hg
  have hm' := mul_nonneg ht hg'
  constructor <;> nlinarith only [hcomp,hopp,hm,hm']

theorem second_phase_preserves_complement {lam p R P delta : ℝ}
    (hL : 0 ≤ lam) (hd : 0 ≤ delta) (hcomp : (1-p)*R ≤ lam*P) :
    (1-p)*R ≤ lam*(P+delta) := by
  have hh := mul_nonneg hL hd
  nlinarith

end OptimalG
