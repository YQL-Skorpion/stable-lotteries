import OptimalG.Certificates.Interval

/-! Computable rational polynomials and exact equality checks. -/
namespace OptimalG.Certificates

abbrev RationalPolynomial := List ℚ
namespace RationalPolynomial

noncomputable def eval : RationalPolynomial → ℝ → ℝ
  | [], _ => 0
  | c::cs, t => (c:ℝ)+t*eval cs t

def add : RationalPolynomial → RationalPolynomial → RationalPolynomial
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::add p q

def scale (c : ℚ) (p : RationalPolynomial) : RationalPolynomial := p.map (c*·)

def mul : RationalPolynomial → RationalPolynomial → RationalPolynomial
  | [], _ => []
  | a::p, q => add (scale a q) (0::mul p q)

def pow (p : RationalPolynomial) : ℕ → RationalPolynomial
  | 0 => [1]
  | n+1 => mul p (pow p n)

def compose : RationalPolynomial → RationalPolynomial → RationalPolynomial
  | [], _ => []
  | c::p, q => add [c] (mul q (compose p q))

def eqCheck (p q : RationalPolynomial) : Bool := (add p (scale (-1) q)).all (fun c => decide (c=0))

@[simp] theorem eval_add (p q : RationalPolynomial) (t : ℝ) :
    eval (add p q) t=eval p t+eval q t := by
  induction p generalizing q with
  | nil => simp [add,eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add,eval]
    | cons b q => simp only [add,eval,Rat.cast_add,ih]; ring

@[simp] theorem eval_scale (c : ℚ) (p : RationalPolynomial) (t : ℝ) :
    eval (scale c p) t=(c:ℝ)*eval p t := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih => simp only [scale,List.map_cons,eval,Rat.cast_mul] at *; rw [ih]; ring

@[simp] theorem eval_mul (p q : RationalPolynomial) (t : ℝ) :
    eval (mul p q) t=eval p t*eval q t := by
  induction p with
  | nil => simp [mul,eval]
  | cons a p ih => simp only [mul,eval_add,eval_scale,eval,Rat.cast_zero,ih]; ring

@[simp] theorem eval_pow (p : RationalPolynomial) (n : ℕ) (t : ℝ) :
    eval (pow p n) t=(eval p t)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => simp only [pow,eval_mul,ih]; ring

@[simp] theorem eval_compose (p q : RationalPolynomial) (t : ℝ) :
    eval (compose p q) t=eval p (eval q t) := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [compose,eval_add,eval_mul,eval,ih]; ring

theorem eval_eq_zero {p : RationalPolynomial}
    (hp : p.all (fun c => decide (c=0))=true) (t : ℝ) : eval p t=0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have h : a=0 ∧ p.all (fun c => decide (c=0))=true := by
      simpa only [List.all_cons,Bool.and_eq_true,decide_eq_true_eq] using hp
    simp [eval,h.1,ih h.2]

theorem eqCheck_sound {p q : RationalPolynomial} (hc : eqCheck p q=true) (t : ℝ) :
    eval p t=eval q t := by
  have hh := eval_eq_zero hc t
  simp only [eval_add,eval_scale,Rat.cast_neg,Rat.cast_one] at hh
  linarith

/-- One exact de Casteljau step. It mixes neighboring polynomials with weights
`1-t` and `t`, so nonnegativity is preserved throughout the unit interval. -/
def blend : List RationalPolynomial → List RationalPolynomial
  | a::b::rest => add (mul [1,-1] a) (mul [0,1] b)::blend (b::rest)
  | _ => []

def interpolate (ps : List RationalPolynomial) : ℕ → List RationalPolynomial
  | 0 => ps
  | n+1 => blend (interpolate ps n)

def bernstein (bs : List ℚ) : RationalPolynomial :=
  (interpolate (bs.map (fun b => [b])) (bs.length-1)).headD []

def bernsteinCheck (p : RationalPolynomial) (bs : List ℚ) : Bool :=
  bs.all (fun b => decide (0≤b)) && eqCheck p (bernstein bs)

theorem blend_nonnegative {ps : List RationalPolynomial} {t : ℝ}
    (ht : t∈Set.Icc 0 1) (hp : ∀ p∈ps, 0≤eval p t) :
    ∀ p∈blend ps, 0≤eval p t := by
  induction ps with
  | nil => simp [blend]
  | cons a rest ih =>
    cases rest with
    | nil => simp [blend]
    | cons b tail =>
      intro p h
      simp only [blend,List.mem_cons] at h
      rcases h with rfl | h
      · have ha := hp a (by simp)
        have hb := hp b (by simp)
        simp only [eval_add,eval_mul,eval,Rat.cast_one,Rat.cast_neg,Rat.cast_zero]
        nlinarith [mul_nonneg (show 0≤1-t by linarith [ht.2]) ha,mul_nonneg ht.1 hb]
      · exact ih (fun q hq => hp q (List.mem_cons_of_mem a hq)) p h

theorem interpolate_nonnegative {ps : List RationalPolynomial} {t : ℝ}
    (ht : t∈Set.Icc 0 1) (hp : ∀ p∈ps, 0≤eval p t) (n : ℕ) :
    ∀ p∈interpolate ps n, 0≤eval p t := by
  induction n with
  | zero => exact hp
  | succ n ih => exact blend_nonnegative ht ih

theorem bernstein_nonnegative {bs : List ℚ} (hb : bs.all (fun b => decide (0≤b))=true)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : 0≤eval (bernstein bs) t := by
  have hp : ∀ p∈bs.map (fun b => [b]), 0≤eval p t := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨b,hb',rfl⟩
    have hn : (0:ℚ)≤b := of_decide_eq_true (List.all_eq_true.mp hb b hb')
    have hn' : (0:ℝ)≤b := by exact_mod_cast hn
    simpa [eval] using hn'
  have hi := interpolate_nonnegative ht hp (bs.length-1)
  unfold bernstein
  cases he : interpolate (bs.map (fun b => [b])) (bs.length-1) with
  | nil => simp [List.headD,eval]
  | cons p ps =>
    simp only [List.headD]
    exact hi p (by rw [he]; simp)

theorem bernsteinCheck_sound {p : RationalPolynomial} {bs : List ℚ}
    (hc : bernsteinCheck p bs=true) {t : ℝ} (ht : t∈Set.Icc 0 1) : 0≤eval p t := by
  have h : bs.all (fun b => decide (0≤b))=true ∧ eqCheck p (bernstein bs)=true := by
    simpa only [bernsteinCheck,Bool.and_eq_true] using hc
  rw [eqCheck_sound h.2]
  exact bernstein_nonnegative h.1 ht

end RationalPolynomial
end OptimalG.Certificates
