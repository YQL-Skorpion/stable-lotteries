import OptimalG.Certificates.Interval

/-! Exact degree-five Bernstein positivity certificates, allowing endpoint zeros. -/

namespace OptimalG.Certificates

structure PowerPolynomial5 where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
  a5 : ℚ
  deriving DecidableEq, Repr

namespace PowerPolynomial5

noncomputable def eval (p : PowerPolynomial5) (t : ℝ) : ℝ :=
  p.a0+p.a1*t+p.a2*t^2+p.a3*t^3+p.a4*t^4+p.a5*t^5

def b0 (p : PowerPolynomial5) : ℚ := p.a0
def b1 (p : PowerPolynomial5) : ℚ := p.a0+p.a1/5
def b2 (p : PowerPolynomial5) : ℚ := p.a0+2*p.a1/5+p.a2/10
def b3 (p : PowerPolynomial5) : ℚ := p.a0+3*p.a1/5+3*p.a2/10+p.a3/10
def b4 (p : PowerPolynomial5) : ℚ := p.a0+4*p.a1/5+3*p.a2/5+2*p.a3/5+p.a4/5
def b5 (p : PowerPolynomial5) : ℚ := p.a0+p.a1+p.a2+p.a3+p.a4+p.a5

theorem bernstein_identity (p : PowerPolynomial5) (t : ℝ) :
    p.eval t = (p.b0:ℝ)*(1-t)^5+5*p.b1*t*(1-t)^4+10*p.b2*t^2*(1-t)^3+
      10*p.b3*t^3*(1-t)^2+5*p.b4*t^4*(1-t)+p.b5*t^5 := by
  simp only [eval,b0,b1,b2,b3,b4,b5,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
  ring

def nonnegativeCheck (p : PowerPolynomial5) : Bool := decide
  (0≤p.b0 ∧ 0≤p.b1 ∧ 0≤p.b2 ∧ 0≤p.b3 ∧ 0≤p.b4 ∧ 0≤p.b5)

theorem nonnegativeCheck_sound {p : PowerPolynomial5} (hp : p.nonnegativeCheck=true)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : 0≤p.eval t := by
  have hq : 0≤p.b0 ∧ 0≤p.b1 ∧ 0≤p.b2 ∧ 0≤p.b3 ∧ 0≤p.b4 ∧ 0≤p.b5 := by
    simpa only [nonnegativeCheck,decide_eq_true_eq] using hp
  have h0 : (0:ℝ)≤p.b0 := by exact_mod_cast hq.1
  have h1 : (0:ℝ)≤p.b1 := by exact_mod_cast hq.2.1
  have h2 : (0:ℝ)≤p.b2 := by exact_mod_cast hq.2.2.1
  have h3 : (0:ℝ)≤p.b3 := by exact_mod_cast hq.2.2.2.1
  have h4 : (0:ℝ)≤p.b4 := by exact_mod_cast hq.2.2.2.2.1
  have h5 : (0:ℝ)≤p.b5 := by exact_mod_cast hq.2.2.2.2.2
  have ht0 : 0≤t := ht.1
  have ht1 : 0≤1-t := sub_nonneg.mpr ht.2
  rw [bernstein_identity]
  positivity

end PowerPolynomial5
end OptimalG.Certificates
