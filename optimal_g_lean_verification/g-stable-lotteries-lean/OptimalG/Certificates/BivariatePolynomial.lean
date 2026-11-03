import OptimalG.Certificates.RationalPolynomial

/-! Tensor-product positivity certificates: an exact cubic in the second variable
whose four Bernstein coefficients are checked rational polynomials in the first. -/
namespace OptimalG.Certificates

structure BivariatePolynomial3 where
  c0 : RationalPolynomial
  c1 : RationalPolynomial
  c2 : RationalPolynomial
  c3 : RationalPolynomial
  deriving Repr

structure BivariateCertificate3 where
  b0 : List ℚ
  b1 : List ℚ
  b2 : List ℚ
  b3 : List ℚ
  deriving Repr

namespace BivariatePolynomial3
open RationalPolynomial

noncomputable def eval (p : BivariatePolynomial3) (t u : ℝ) : ℝ :=
  p.c0.eval t+u*p.c1.eval t+u^2*p.c2.eval t+u^3*p.c3.eval t

def b0 (p : BivariatePolynomial3) : RationalPolynomial := p.c0
def b1 (p : BivariatePolynomial3) : RationalPolynomial := add p.c0 (scale (1/3) p.c1)
def b2 (p : BivariatePolynomial3) : RationalPolynomial := add (add p.c0 (scale (2/3) p.c1)) (scale (1/3) p.c2)
def b3 (p : BivariatePolynomial3) : RationalPolynomial := add (add (add p.c0 p.c1) p.c2) p.c3

def check (p : BivariatePolynomial3) (c : BivariateCertificate3) : Bool :=
  bernsteinCheck p.b0 c.b0 && (bernsteinCheck p.b1 c.b1 &&
    (bernsteinCheck p.b2 c.b2 && bernsteinCheck p.b3 c.b3))

theorem bernstein_identity (p : BivariatePolynomial3) (t u : ℝ) :
    p.eval t u=(1-u)^3*p.b0.eval t+3*u*(1-u)^2*p.b1.eval t+
      3*u^2*(1-u)*p.b2.eval t+u^3*p.b3.eval t := by
  simp only [eval,b0,b1,b2,b3,eval_add,eval_scale,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  ring

theorem check_sound {p : BivariatePolynomial3} {c : BivariateCertificate3}
    (hc : p.check c=true) {t u : ℝ} (ht : t∈Set.Icc 0 1) (hu : u∈Set.Icc 0 1) :
    0≤p.eval t u := by
  have h : bernsteinCheck p.b0 c.b0=true ∧ bernsteinCheck p.b1 c.b1=true ∧
      bernsteinCheck p.b2 c.b2=true ∧ bernsteinCheck p.b3 c.b3=true := by
    simpa only [check,Bool.and_eq_true] using hc
  have h0 := bernsteinCheck_sound h.1 ht
  have h1 := bernsteinCheck_sound h.2.1 ht
  have h2 := bernsteinCheck_sound h.2.2.1 ht
  have h3 := bernsteinCheck_sound h.2.2.2 ht
  have hu0 : 0≤u := hu.1
  have hu1 : 0≤1-u := sub_nonneg.mpr hu.2
  rw [bernstein_identity]
  positivity

/-- Substitute `q=lo+width*u`, exactly. -/
def affineSecond (p : BivariatePolynomial3) (lo width : ℚ) : BivariatePolynomial3 :=
  ⟨add (add (add p.c0 (scale lo p.c1)) (scale (lo^2) p.c2)) (scale (lo^3) p.c3),
   scale width (add (add p.c1 (scale (2*lo) p.c2)) (scale (3*lo^2) p.c3)),
   scale (width^2) (add p.c2 (scale (3*lo) p.c3)),scale (width^3) p.c3⟩

theorem affineSecond_eval (p : BivariatePolynomial3) (lo width : ℚ) (t u : ℝ) :
    (p.affineSecond lo width).eval t u=p.eval t ((lo:ℝ)+(width:ℝ)*u) := by
  simp only [affineSecond,eval,eval_add,eval_scale,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  ring

end BivariatePolynomial3
end OptimalG.Certificates
