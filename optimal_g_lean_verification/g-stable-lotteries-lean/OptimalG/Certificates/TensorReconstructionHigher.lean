import OptimalG.Certificates.TensorReconstruction
import OptimalG.Certificates.TensorBernstein5

/-! Exact nested Horner reconstruction in four and five coordinates. -/
namespace OptimalG.Certificates

abbrev RationalPolynomial4 := List RationalPolynomial3
namespace RationalPolynomial4
noncomputable def eval : RationalPolynomial4 → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _ => 0
  | p::ps, u, v, w, x => p.eval v w x+u*eval ps u v w x

def add : RationalPolynomial4 → RationalPolynomial4 → RationalPolynomial4
  | [], q => q
  | p, [] => p
  | a::p, b::q => RationalPolynomial3.add a b::add p q

def scale (c : ℚ) (p : RationalPolynomial4) : RationalPolynomial4 := p.map (RationalPolynomial3.scale c)

def mulFirst : RationalPolynomial → RationalPolynomial4 → RationalPolynomial4
  | [], _ => []
  | a::p, q => add (scale a q) ([]::mulFirst p q)

def composeFirst : RationalPolynomial4 → RationalPolynomial → RationalPolynomial4
  | [], _ => []
  | a::p, q => add [a] (mulFirst q (composeFirst p q))

def composeRest (p : RationalPolynomial4) (b c d : RationalPolynomial) : RationalPolynomial4 :=
  p.map (fun q=>q.compose b c d)

def compose (p : RationalPolynomial4) (a b c d : RationalPolynomial) : RationalPolynomial4 :=
  (p.composeFirst a).composeRest b c d

def eqCheck : RationalPolynomial4 → RationalPolynomial4 → Bool
  | [], q => q.all (fun a=>a.eqCheck [])
  | p, [] => p.all (fun a=>a.eqCheck [])
  | a::p, b::q => a.eqCheck b && eqCheck p q

@[simp] theorem eval_add (p q : RationalPolynomial4) (u v w x : ℝ) :
    (add p q).eval u v w x=p.eval u v w x+q.eval u v w x := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,RationalPolynomial3.eval_add,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : RationalPolynomial4) (u v w x : ℝ) :
    (scale c p).eval u v w x=(c:ℝ)*p.eval u v w x := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,RationalPolynomial3.eval_scale] at *; rw [ih]; ring

@[simp] theorem eval_mulFirst (p : RationalPolynomial) (q : RationalPolynomial4) (u v w x : ℝ) :
    (mulFirst p q).eval u v w x=p.eval u*q.eval u v w x := by
  induction p with
  | nil => simp [mulFirst,eval,RationalPolynomial.eval]
  | cons a p ih =>
    simp only [mulFirst,eval_add,eval_scale,eval,RationalPolynomial3.eval,RationalPolynomial.eval,ih]
    ring

@[simp] theorem eval_composeFirst (p : RationalPolynomial4) (q : RationalPolynomial) (u v w x : ℝ) :
    (composeFirst p q).eval u v w x=p.eval (q.eval u) v w x := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [composeFirst,eval_add,eval_mulFirst,eval,ih]; ring

@[simp] theorem eval_composeRest (p : RationalPolynomial4) (b c d : RationalPolynomial) (u v w x : ℝ) :
    (composeRest p b c d).eval u v w x=p.eval u (b.eval v) (c.eval w) (d.eval x) := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    simp only [composeRest,List.map_cons,eval,RationalPolynomial3.eval_compose] at *
    rw [ih]

@[simp] theorem eval_compose (p : RationalPolynomial4) (a b c d : RationalPolynomial) (u v w x : ℝ) :
    (p.compose a b c d).eval u v w x=p.eval (a.eval u) (b.eval v) (c.eval w) (d.eval x) := by
  simp only [compose,eval_composeRest,eval_composeFirst]

theorem eval_zero {p : RationalPolynomial4}
    (hp : p.all (fun a=>a.eqCheck [])=true) (u v w x : ℝ) : p.eval u v w x=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : a.eqCheck []=true ∧ p.all (fun a=>a.eqCheck [])=true := by
      simpa only [List.all_cons,Bool.and_eq_true_iff] using hp
    have ha := RationalPolynomial3.eqCheck_sound hh.1 v w x
    simp only [eval,ha,RationalPolynomial3.eval,ih hh.2,mul_zero,add_zero]

theorem eqCheck_sound {p q : RationalPolynomial4} (hc : eqCheck p q=true) (u v w x : ℝ) :
    p.eval u v w x=q.eval u v w x := by
  induction p generalizing q with
  | nil => exact (eval_zero hc u v w x).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_zero hc u v w x
    | cons b q =>
      have hh := Bool.and_eq_true_iff.mp hc
      simp only [eval,RationalPolynomial3.eqCheck_sound hh.1 v w x,ih hh.2]

/-- Product of univariate polynomial factors. -/
def tensor (a b c d : RationalPolynomial) : RationalPolynomial4 :=
  a.map (fun r=>(RationalPolynomial3.tensor b c d).scale r)

theorem eval_tensor (a b c d : RationalPolynomial) (u v w x : ℝ) :
    (tensor a b c d).eval u v w x=a.eval u*b.eval v*c.eval w*d.eval x := by
  induction a with
  | nil => simp [tensor,eval,RationalPolynomial.eval]
  | cons r a ih =>
    simp only [tensor,List.map_cons,eval,RationalPolynomial3.eval_scale,RationalPolynomial3.eval_tensor,RationalPolynomial.eval] at *
    rw [ih]
    ring

end RationalPolynomial4

abbrev RationalPolynomial5 := List RationalPolynomial4
namespace RationalPolynomial5
noncomputable def eval : RationalPolynomial5 → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _, _, _ => 0
  | p::ps, u, v, w, x, y => p.eval v w x y+u*eval ps u v w x y

def add : RationalPolynomial5 → RationalPolynomial5 → RationalPolynomial5
  | [], q => q
  | p, [] => p
  | a::p, b::q => RationalPolynomial4.add a b::add p q

def scale (c : ℚ) (p : RationalPolynomial5) : RationalPolynomial5 := p.map (RationalPolynomial4.scale c)

def mulFirst : RationalPolynomial → RationalPolynomial5 → RationalPolynomial5
  | [], _ => []
  | a::p, q => add (scale a q) ([]::mulFirst p q)

def composeFirst : RationalPolynomial5 → RationalPolynomial → RationalPolynomial5
  | [], _ => []
  | a::p, q => add [a] (mulFirst q (composeFirst p q))

def composeRest (p : RationalPolynomial5) (b c d e : RationalPolynomial) : RationalPolynomial5 :=
  p.map (fun q=>q.compose b c d e)

def compose (p : RationalPolynomial5) (a b c d e : RationalPolynomial) : RationalPolynomial5 :=
  (p.composeFirst a).composeRest b c d e

def eqCheck : RationalPolynomial5 → RationalPolynomial5 → Bool
  | [], q => q.all (fun a=>a.eqCheck [])
  | p, [] => p.all (fun a=>a.eqCheck [])
  | a::p, b::q => a.eqCheck b && eqCheck p q

@[simp] theorem eval_add (p q : RationalPolynomial5) (u v w x y : ℝ) :
    (add p q).eval u v w x y=p.eval u v w x y+q.eval u v w x y := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,RationalPolynomial4.eval_add,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : RationalPolynomial5) (u v w x y : ℝ) :
    (scale c p).eval u v w x y=(c:ℝ)*p.eval u v w x y := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,RationalPolynomial4.eval_scale] at *; rw [ih]; ring

@[simp] theorem eval_mulFirst (p : RationalPolynomial) (q : RationalPolynomial5) (u v w x y : ℝ) :
    (mulFirst p q).eval u v w x y=p.eval u*q.eval u v w x y := by
  induction p with
  | nil => simp [mulFirst,eval,RationalPolynomial.eval]
  | cons a p ih =>
    simp only [mulFirst,eval_add,eval_scale,eval,RationalPolynomial4.eval,RationalPolynomial.eval,ih]
    ring

@[simp] theorem eval_composeFirst (p : RationalPolynomial5) (q : RationalPolynomial) (u v w x y : ℝ) :
    (composeFirst p q).eval u v w x y=p.eval (q.eval u) v w x y := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [composeFirst,eval_add,eval_mulFirst,eval,ih]; ring

@[simp] theorem eval_composeRest (p : RationalPolynomial5) (b c d e : RationalPolynomial) (u v w x y : ℝ) :
    (composeRest p b c d e).eval u v w x y=p.eval u (b.eval v) (c.eval w) (d.eval x) (e.eval y) := by
  induction p with
  | nil => rfl
  | cons q p ih =>
    simp only [composeRest,List.map_cons,eval,RationalPolynomial4.eval_compose] at *
    rw [ih]

@[simp] theorem eval_compose (p : RationalPolynomial5) (a b c d e : RationalPolynomial) (u v w x y : ℝ) :
    (p.compose a b c d e).eval u v w x y=p.eval (a.eval u) (b.eval v) (c.eval w) (d.eval x) (e.eval y) := by
  simp only [compose,eval_composeRest,eval_composeFirst]

theorem eval_zero {p : RationalPolynomial5}
    (hp : p.all (fun a=>a.eqCheck [])=true) (u v w x y : ℝ) : p.eval u v w x y=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hh : a.eqCheck []=true ∧ p.all (fun a=>a.eqCheck [])=true := by
      simpa only [List.all_cons,Bool.and_eq_true_iff] using hp
    have ha := RationalPolynomial4.eqCheck_sound hh.1 v w x y
    simp only [eval,ha,RationalPolynomial4.eval,ih hh.2,mul_zero,add_zero]

theorem eqCheck_sound {p q : RationalPolynomial5} (hc : eqCheck p q=true) (u v w x y : ℝ) :
    p.eval u v w x y=q.eval u v w x y := by
  induction p generalizing q with
  | nil => exact (eval_zero hc u v w x y).symm
  | cons a p ih =>
    cases q with
    | nil => exact eval_zero hc u v w x y
    | cons b q =>
      have hh := Bool.and_eq_true_iff.mp hc
      simp only [eval,RationalPolynomial4.eqCheck_sound hh.1 v w x y,ih hh.2]

/-- Product of univariate polynomial factors. -/
def tensor (a b c d e : RationalPolynomial) : RationalPolynomial5 :=
  a.map (fun r=>(RationalPolynomial4.tensor b c d e).scale r)

theorem eval_tensor (a b c d e : RationalPolynomial) (u v w x y : ℝ) :
    (tensor a b c d e).eval u v w x y=a.eval u*b.eval v*c.eval w*d.eval x*e.eval y := by
  induction a with
  | nil => simp [tensor,eval,RationalPolynomial.eval]
  | cons r a ih =>
    simp only [tensor,List.map_cons,eval,RationalPolynomial4.eval_scale,RationalPolynomial4.eval_tensor,RationalPolynomial.eval] at *
    rw [ih]
    ring

end RationalPolynomial5

namespace TensorBernsteinTerm5

def polynomial (t : TensorBernsteinTerm5) : RationalPolynomial5 :=
  let basis (n m : ℕ) := RationalPolynomial.mul
    (RationalPolynomial.pow [0,1] n) (RationalPolynomial.pow [1,-1] m)
  (RationalPolynomial5.tensor (basis t.a t.ac) (basis t.b t.bc)
    (basis t.c t.cc) (basis t.d t.dc) (basis t.e t.ec)).scale t.coefficient

theorem polynomial_eval (t : TensorBernsteinTerm5) (a b c d e : ℝ) :
    t.polynomial.eval a b c d e=t.eval a b c d e := by
  simp only [polynomial,RationalPolynomial5.eval_scale,RationalPolynomial5.eval_tensor,
    RationalPolynomial.eval_mul,RationalPolynomial.eval_pow,RationalPolynomial.eval,
    Rat.cast_zero,Rat.cast_one,Rat.cast_neg,zero_mul,mul_zero,add_zero,zero_add,mul_one,mul_neg]
  dsimp [eval]
  ring
end TensorBernsteinTerm5

namespace TensorBernstein5

def polynomial (ts : TensorBernstein5) : RationalPolynomial5 :=
  (ts.map TensorBernsteinTerm5.polynomial).foldr RationalPolynomial5.add []

theorem polynomial_eval (ts : TensorBernstein5) (a b c d e : ℝ) :
    ts.polynomial.eval a b c d e=ts.eval a b c d e := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [polynomial,List.map_cons,List.foldr_cons,RationalPolynomial5.eval_add,
      TensorBernsteinTerm5.polynomial_eval,eval,List.sum_cons] at *
    rw [ih]

def reconstructCheck (ts : TensorBernstein5) (p : RationalPolynomial5) : Bool :=
  ts.check && p.eqCheck ts.polynomial

theorem reconstructCheck_sound {ts : TensorBernstein5} {p : RationalPolynomial5}
    (hc : ts.reconstructCheck p=true) {a b c d e : ℝ}
    (ha : a∈Set.Icc 0 1) (hb : b∈Set.Icc 0 1) (hcc : c∈Set.Icc 0 1)
    (hd : d∈Set.Icc 0 1) (he : e∈Set.Icc 0 1) :
    0≤p.eval a b c d e := by
  have hh := Bool.and_eq_true_iff.mp hc
  rw [RationalPolynomial5.eqCheck_sound hh.2 a b c d e,polynomial_eval]
  exact check_sound hh.1 ha hb hcc hd he

end TensorBernstein5
end OptimalG.Certificates
