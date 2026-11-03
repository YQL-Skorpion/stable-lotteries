import OptimalG.Certificates.TensorReconstructionHigher

/-! Full multiplication and powers for nested rational Horner polynomials.
The equality checker can certify arithmetic identities without expanding their
real-valued interpretations into a large tactic proof. -/
namespace OptimalG.Certificates

namespace RationalPolynomial2

def mulRest (a : RationalPolynomial) (p : RationalPolynomial2) : RationalPolynomial2 :=
  p.map (RationalPolynomial.mul a)

def mul : RationalPolynomial2 → RationalPolynomial2 → RationalPolynomial2
  | [], _ => []
  | a::p, q => add (mulRest a q) ([]::mul p q)

def pow (p : RationalPolynomial2) : ℕ → RationalPolynomial2
  | 0 => [[1]]
  | n+1 => mul p (pow p n)

@[simp] theorem eval_mulRest (a : RationalPolynomial) (p : RationalPolynomial2) (u v : ℝ) :
    (mulRest a p).eval u v=a.eval v*p.eval u v := by
  induction p with
  | nil => simp [mulRest,eval]
  | cons b p ih =>
    simp only [mulRest,List.map_cons,eval,RationalPolynomial.eval_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_mul (p q : RationalPolynomial2) (u v : ℝ) :
    (mul p q).eval u v=p.eval u v*q.eval u v := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    simp only [mul,eval_add,eval_mulRest,eval,RationalPolynomial.eval,ih]
    ring

@[simp] theorem eval_pow (p : RationalPolynomial2) (n : ℕ) (u v : ℝ) :
    (pow p n).eval u v=(p.eval u v)^n := by
  induction n with
  | zero => simp [pow,RationalPolynomial.eval,RationalPolynomial2.eval]
  | succ k ih => simp only [pow,eval_mul,ih]; ring

end RationalPolynomial2

namespace RationalPolynomial3

def mulRest (a : RationalPolynomial2) (p : RationalPolynomial3) : RationalPolynomial3 :=
  p.map (RationalPolynomial2.mul a)

def mul : RationalPolynomial3 → RationalPolynomial3 → RationalPolynomial3
  | [], _ => []
  | a::p, q => add (mulRest a q) ([]::mul p q)

def pow (p : RationalPolynomial3) : ℕ → RationalPolynomial3
  | 0 => [[[1]]]
  | n+1 => mul p (pow p n)

@[simp] theorem eval_mulRest (a : RationalPolynomial2) (p : RationalPolynomial3) (u v w : ℝ) :
    (mulRest a p).eval u v w=a.eval v w*p.eval u v w := by
  induction p with
  | nil => simp [mulRest,eval]
  | cons b p ih =>
    simp only [mulRest,List.map_cons,eval,RationalPolynomial2.eval_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_mul (p q : RationalPolynomial3) (u v w : ℝ) :
    (mul p q).eval u v w=p.eval u v w*q.eval u v w := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    simp only [mul,eval_add,eval_mulRest,eval,RationalPolynomial2.eval,ih]
    ring

@[simp] theorem eval_pow (p : RationalPolynomial3) (n : ℕ) (u v w : ℝ) :
    (pow p n).eval u v w=(p.eval u v w)^n := by
  induction n with
  | zero => simp [pow,RationalPolynomial.eval,RationalPolynomial2.eval,RationalPolynomial3.eval]
  | succ k ih => simp only [pow,eval_mul,ih]; ring

end RationalPolynomial3

namespace RationalPolynomial4

def mulRest (a : RationalPolynomial3) (p : RationalPolynomial4) : RationalPolynomial4 :=
  p.map (RationalPolynomial3.mul a)

def mul : RationalPolynomial4 → RationalPolynomial4 → RationalPolynomial4
  | [], _ => []
  | a::p, q => add (mulRest a q) ([]::mul p q)

def pow (p : RationalPolynomial4) : ℕ → RationalPolynomial4
  | 0 => [[[[1]]]]
  | n+1 => mul p (pow p n)

@[simp] theorem eval_mulRest (a : RationalPolynomial3) (p : RationalPolynomial4) (u v w x : ℝ) :
    (mulRest a p).eval u v w x=a.eval v w x*p.eval u v w x := by
  induction p with
  | nil => simp [mulRest,eval]
  | cons b p ih =>
    simp only [mulRest,List.map_cons,eval,RationalPolynomial3.eval_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_mul (p q : RationalPolynomial4) (u v w x : ℝ) :
    (mul p q).eval u v w x=p.eval u v w x*q.eval u v w x := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    simp only [mul,eval_add,eval_mulRest,eval,RationalPolynomial3.eval,ih]
    ring

@[simp] theorem eval_pow (p : RationalPolynomial4) (n : ℕ) (u v w x : ℝ) :
    (pow p n).eval u v w x=(p.eval u v w x)^n := by
  induction n with
  | zero => simp [pow,RationalPolynomial.eval,RationalPolynomial2.eval,RationalPolynomial3.eval,RationalPolynomial4.eval]
  | succ k ih => simp only [pow,eval_mul,ih]; ring

end RationalPolynomial4

namespace RationalPolynomial5

def mulRest (a : RationalPolynomial4) (p : RationalPolynomial5) : RationalPolynomial5 :=
  p.map (RationalPolynomial4.mul a)

def mul : RationalPolynomial5 → RationalPolynomial5 → RationalPolynomial5
  | [], _ => []
  | a::p, q => add (mulRest a q) ([]::mul p q)

def pow (p : RationalPolynomial5) : ℕ → RationalPolynomial5
  | 0 => [[[[[1]]]]]
  | n+1 => mul p (pow p n)

@[simp] theorem eval_mulRest (a : RationalPolynomial4) (p : RationalPolynomial5) (u v w x y : ℝ) :
    (mulRest a p).eval u v w x y=a.eval v w x y*p.eval u v w x y := by
  induction p with
  | nil => simp [mulRest,eval]
  | cons b p ih =>
    simp only [mulRest,List.map_cons,eval,RationalPolynomial4.eval_mul] at *
    rw [ih]
    ring

@[simp] theorem eval_mul (p q : RationalPolynomial5) (u v w x y : ℝ) :
    (mul p q).eval u v w x y=p.eval u v w x y*q.eval u v w x y := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih =>
    simp only [mul,eval_add,eval_mulRest,eval,RationalPolynomial4.eval,ih]
    ring

@[simp] theorem eval_pow (p : RationalPolynomial5) (n : ℕ) (u v w x y : ℝ) :
    (pow p n).eval u v w x y=(p.eval u v w x y)^n := by
  induction n with
  | zero => simp [pow,RationalPolynomial.eval,RationalPolynomial2.eval,RationalPolynomial3.eval,RationalPolynomial4.eval,RationalPolynomial5.eval]
  | succ k ih => simp only [pow,eval_mul,ih]; ring

end RationalPolynomial5

end OptimalG.Certificates
