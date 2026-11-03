import OptimalG.Certificates.TensorBernstein

/-! Exact computational reconstruction of three-variable Bernstein certificates.
Each polynomial is a nested Horner list. Equality is checked coefficientwise,
so a certificate needs no large real-arithmetic normalization proof. -/
namespace OptimalG.Certificates

abbrev RationalPolynomial2 := List RationalPolynomial
namespace RationalPolynomial2
noncomputable def eval : RationalPolynomial2 → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | p::ps, y, z => p.eval z+y*eval ps y z

def add : RationalPolynomial2 → RationalPolynomial2 → RationalPolynomial2
  | [], q => q
  | p, [] => p
  | a::p, b::q => RationalPolynomial.add a b::add p q

def scale (c : ℚ) (p : RationalPolynomial2) : RationalPolynomial2 :=
  p.map (RationalPolynomial.scale c)

def mulFirst : RationalPolynomial → RationalPolynomial2 → RationalPolynomial2
  | [], _ => []
  | a::p, q => add (scale a q) ([]::mulFirst p q)

def composeFirst : RationalPolynomial2 → RationalPolynomial → RationalPolynomial2
  | [], _ => []
  | a::p, q => add [a] (mulFirst q (composeFirst p q))

def composeSecond (p : RationalPolynomial2) (q : RationalPolynomial) : RationalPolynomial2 :=
  p.map (fun a=>a.compose q)

def eqCheck : RationalPolynomial2 → RationalPolynomial2 → Bool
  | [], q => q.all (fun a=>a.eqCheck [])
  | p, [] => p.all (fun a=>a.eqCheck [])
  | a::p, b::q => a.eqCheck b && eqCheck p q

@[simp] theorem eval_add (p q : RationalPolynomial2) (y z : ℝ) :
    (add p q).eval y z=p.eval y z+q.eval y z := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,RationalPolynomial.eval_add,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : RationalPolynomial2) (y z : ℝ) :
    (scale c p).eval y z=(c:ℝ)*p.eval y z := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,RationalPolynomial.eval_scale] at *; rw [ih]; ring

@[simp] theorem eval_mulFirst (p : RationalPolynomial) (q : RationalPolynomial2) (y z : ℝ) :
    (mulFirst p q).eval y z=p.eval y*q.eval y z := by
  induction p with
  | nil => simp [mulFirst,eval,RationalPolynomial.eval]
  | cons a p ih =>
    simp only [mulFirst,eval_add,eval_scale,eval,RationalPolynomial2.eval,RationalPolynomial.eval,ih]
    ring

@[simp] theorem eval_composeFirst (p : RationalPolynomial2) (q : RationalPolynomial) (y z : ℝ) :
    (composeFirst p q).eval y z=p.eval (q.eval y) z := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [composeFirst,eval_add,eval_mulFirst,eval,ih]; ring

@[simp] theorem eval_composeSecond (p : RationalPolynomial2) (q : RationalPolynomial) (y z : ℝ) :
    (composeSecond p q).eval y z=p.eval y (q.eval z) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [composeSecond,List.map_cons,eval,RationalPolynomial.eval_compose] at *
    rw [ih]

theorem eval_zero {p : RationalPolynomial2}
    (hp : p.all (fun a=>a.eqCheck [])=true) (y z : ℝ) : p.eval y z=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : a.eqCheck []=true ∧ p.all (fun a=>a.eqCheck [])=true := by
      simpa only [List.all_cons,Bool.and_eq_true_iff] using hp
    have ha := RationalPolynomial.eqCheck_sound hh.1 z
    simp only [eval,ha,RationalPolynomial.eval,ih hh.2,mul_zero,add_zero]

theorem eqCheck_sound {p q : RationalPolynomial2} (hc : eqCheck p q=true) (y z : ℝ) :
    p.eval y z=q.eval y z := by
  induction p generalizing q with
  | nil => exact (eval_zero hc y z).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_zero hc y z
    | cons b q =>
      have hh := Bool.and_eq_true_iff.mp hc
      simp only [eval,RationalPolynomial.eqCheck_sound hh.1 z,ih hh.2]

end RationalPolynomial2

abbrev RationalPolynomial3 := List RationalPolynomial2
namespace RationalPolynomial3
noncomputable def eval : RationalPolynomial3 → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | p::ps, x, y, z => p.eval y z+x*eval ps x y z

def add : RationalPolynomial3 → RationalPolynomial3 → RationalPolynomial3
  | [], q => q
  | p, [] => p
  | a::p, b::q => RationalPolynomial2.add a b::add p q

def scale (c : ℚ) (p : RationalPolynomial3) : RationalPolynomial3 :=
  p.map (RationalPolynomial2.scale c)

def mulFirst : RationalPolynomial → RationalPolynomial3 → RationalPolynomial3
  | [], _ => []
  | a::p, q => add (scale a q) ([]::mulFirst p q)

def composeFirst : RationalPolynomial3 → RationalPolynomial → RationalPolynomial3
  | [], _ => []
  | a::p, q => add [a] (mulFirst q (composeFirst p q))

def composeRest (p : RationalPolynomial3) (q r : RationalPolynomial) : RationalPolynomial3 :=
  p.map (fun a=>(a.composeFirst q).composeSecond r)

def compose (p : RationalPolynomial3) (a b c : RationalPolynomial) : RationalPolynomial3 :=
  (p.composeFirst a).composeRest b c

def eqCheck : RationalPolynomial3 → RationalPolynomial3 → Bool
  | [], q => q.all (fun a=>a.eqCheck [])
  | p, [] => p.all (fun a=>a.eqCheck [])
  | a::p, b::q => a.eqCheck b && eqCheck p q

@[simp] theorem eval_add (p q : RationalPolynomial3) (x y z : ℝ) :
    (add p q).eval x y z=p.eval x y z+q.eval x y z := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,RationalPolynomial2.eval_add,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : RationalPolynomial3) (x y z : ℝ) :
    (scale c p).eval x y z=(c:ℝ)*p.eval x y z := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,RationalPolynomial2.eval_scale] at *; rw [ih]; ring

@[simp] theorem eval_mulFirst (p : RationalPolynomial) (q : RationalPolynomial3) (x y z : ℝ) :
    (mulFirst p q).eval x y z=p.eval x*q.eval x y z := by
  induction p with
  | nil => simp [mulFirst,eval,RationalPolynomial.eval]
  | cons a p ih =>
    simp only [mulFirst,eval_add,eval_scale,eval,RationalPolynomial2.eval,RationalPolynomial.eval,ih]
    ring

@[simp] theorem eval_composeFirst (p : RationalPolynomial3) (q : RationalPolynomial) (x y z : ℝ) :
    (composeFirst p q).eval x y z=p.eval (q.eval x) y z := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [composeFirst,eval_add,eval_mulFirst,eval,ih]; ring

@[simp] theorem eval_composeRest (p : RationalPolynomial3) (a b : RationalPolynomial) (x y z : ℝ) :
    (composeRest p a b).eval x y z=p.eval x (a.eval y) (b.eval z) := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [composeRest,List.map_cons,eval,RationalPolynomial2.eval_composeFirst,
      RationalPolynomial2.eval_composeSecond] at *
    rw [ih]

@[simp] theorem eval_compose (p : RationalPolynomial3) (a b c : RationalPolynomial) (x y z : ℝ) :
    (p.compose a b c).eval x y z=p.eval (a.eval x) (b.eval y) (c.eval z) := by
  simp only [compose,eval_composeRest,eval_composeFirst]

theorem eval_zero {p : RationalPolynomial3}
    (hp : p.all (fun a=>a.eqCheck [])=true) (x y z : ℝ) : p.eval x y z=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : a.eqCheck []=true ∧ p.all (fun a=>a.eqCheck [])=true := by
      simpa only [List.all_cons,Bool.and_eq_true_iff] using hp
    have ha := RationalPolynomial2.eqCheck_sound hh.1 y z
    simp only [eval,ha,RationalPolynomial2.eval,ih hh.2,mul_zero,add_zero]

theorem eqCheck_sound {p q : RationalPolynomial3} (hc : eqCheck p q=true) (x y z : ℝ) :
    p.eval x y z=q.eval x y z := by
  induction p generalizing q with
  | nil => exact (eval_zero hc x y z).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_zero hc x y z
    | cons b q =>
      have hh := Bool.and_eq_true_iff.mp hc
      simp only [eval,RationalPolynomial2.eqCheck_sound hh.1 y z,ih hh.2]

/-- The product of three univariate polynomials, interpreted exactly. -/
def tensor (a b c : RationalPolynomial) : RationalPolynomial3 :=
  a.map (fun v=>b.map (fun w=>c.scale (v*w)))

theorem eval_tensor (a b c : RationalPolynomial) (x y z : ℝ) :
    (tensor a b c).eval x y z=a.eval x*b.eval y*c.eval z := by
  have inner (v : ℚ) : ∀ b : RationalPolynomial,
      RationalPolynomial2.eval (b.map (fun w=>c.scale (v*w))) y z=(v:ℝ)*b.eval y*c.eval z := by
    intro b
    induction b with
    | nil => simp [RationalPolynomial2.eval,RationalPolynomial.eval]
    | cons w b ih =>
      simp only [List.map_cons,RationalPolynomial2.eval,RationalPolynomial.eval_scale,
        Rat.cast_mul,RationalPolynomial.eval]
      rw [ih]
      ring
  induction a with
  | nil => simp [tensor,eval,RationalPolynomial.eval]
  | cons v a ih =>
    simp only [tensor,List.map_cons,eval,inner,RationalPolynomial.eval] at *
    rw [ih]
    ring

end RationalPolynomial3

namespace TensorBernsteinTerm3

def polynomial (t : TensorBernsteinTerm3) : RationalPolynomial3 :=
  let basis (n m : ℕ) := RationalPolynomial.mul
    (RationalPolynomial.pow [0,1] n) (RationalPolynomial.pow [1,-1] m)
  (RationalPolynomial3.tensor (basis t.x t.xc) (basis t.y t.yc)
    (basis t.z t.zc)).scale t.coefficient

theorem polynomial_eval (t : TensorBernsteinTerm3) (x y z : ℝ) :
    t.polynomial.eval x y z=t.eval x y z := by
  simp only [polynomial,RationalPolynomial3.eval_scale,RationalPolynomial3.eval_tensor,
    RationalPolynomial.eval_mul,RationalPolynomial.eval_pow,RationalPolynomial.eval,
    Rat.cast_zero,Rat.cast_one,Rat.cast_neg,zero_mul,mul_zero,add_zero,zero_add,mul_one,mul_neg]
  dsimp [eval]
  ring
end TensorBernsteinTerm3

namespace TensorBernstein3

def polynomial (ts : TensorBernstein3) : RationalPolynomial3 :=
  (ts.map TensorBernsteinTerm3.polynomial).foldr RationalPolynomial3.add []

theorem polynomial_eval (ts : TensorBernstein3) (x y z : ℝ) :
    ts.polynomial.eval x y z=ts.eval x y z := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [polynomial,List.map_cons,List.foldr_cons,RationalPolynomial3.eval_add,
      TensorBernsteinTerm3.polynomial_eval,eval,List.sum_cons] at *
    rw [ih]

def reconstructCheck (ts : TensorBernstein3) (p : RationalPolynomial3) : Bool :=
  ts.check && p.eqCheck ts.polynomial

theorem reconstructCheck_sound {ts : TensorBernstein3} {p : RationalPolynomial3}
    (hc : ts.reconstructCheck p=true) {x y z : ℝ}
    (hx : x∈Set.Icc 0 1) (hy : y∈Set.Icc 0 1) (hz : z∈Set.Icc 0 1) :
    0≤p.eval x y z := by
  have hh := Bool.and_eq_true_iff.mp hc
  rw [RationalPolynomial3.eqCheck_sound hh.2 x y z,polynomial_eval]
  exact check_sound hh.1 hx hy hz

end TensorBernstein3
end OptimalG.Certificates
