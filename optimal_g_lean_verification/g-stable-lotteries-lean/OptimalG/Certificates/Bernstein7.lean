import OptimalG.Certificates.RationalPolynomial
namespace OptimalG.Certificates
structure PowerPolynomial7 where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
  a5 : ℚ
  a6 : ℚ
  a7 : ℚ
  deriving Repr
namespace PowerPolynomial7
noncomputable def eval (p : PowerPolynomial7) (t : ℝ) : ℝ := p.a0*t^0+p.a1*t^1+p.a2*t^2+p.a3*t^3+p.a4*t^4+p.a5*t^5+p.a6*t^6+p.a7*t^7
def b0 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0
def b1 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(1/7:ℚ)*p.a1
def b2 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(2/7:ℚ)*p.a1+(1/21:ℚ)*p.a2
def b3 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(3/7:ℚ)*p.a1+(1/7:ℚ)*p.a2+(1/35:ℚ)*p.a3
def b4 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(4/7:ℚ)*p.a1+(2/7:ℚ)*p.a2+(4/35:ℚ)*p.a3+(1/35:ℚ)*p.a4
def b5 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(5/7:ℚ)*p.a1+(10/21:ℚ)*p.a2+(2/7:ℚ)*p.a3+(1/7:ℚ)*p.a4+(1/21:ℚ)*p.a5
def b6 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(6/7:ℚ)*p.a1+(5/7:ℚ)*p.a2+(4/7:ℚ)*p.a3+(3/7:ℚ)*p.a4+(2/7:ℚ)*p.a5+(1/7:ℚ)*p.a6
def b7 (p : PowerPolynomial7) : ℚ := (1/1:ℚ)*p.a0+(1/1:ℚ)*p.a1+(1/1:ℚ)*p.a2+(1/1:ℚ)*p.a3+(1/1:ℚ)*p.a4+(1/1:ℚ)*p.a5+(1/1:ℚ)*p.a6+(1/1:ℚ)*p.a7
theorem bernstein_identity (p : PowerPolynomial7) (t : ℝ) :
    p.eval t = 1*(p.b0:ℝ)*t^0*(1-t)^7+7*(p.b1:ℝ)*t^1*(1-t)^6+21*(p.b2:ℝ)*t^2*(1-t)^5+35*(p.b3:ℝ)*t^3*(1-t)^4+35*(p.b4:ℝ)*t^4*(1-t)^3+21*(p.b5:ℝ)*t^5*(1-t)^2+7*(p.b6:ℝ)*t^6*(1-t)^1+1*(p.b7:ℝ)*t^7*(1-t)^0 := by
  simp only [eval,b0,b1,b2,b3,b4,b5,b6,b7,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat]
  ring
def nonnegativeCheck (p : PowerPolynomial7) : Bool := decide (0≤p.b0 ∧ 0≤p.b1 ∧ 0≤p.b2 ∧ 0≤p.b3 ∧ 0≤p.b4 ∧ 0≤p.b5 ∧ 0≤p.b6 ∧ 0≤p.b7)
 theorem nonnegativeCheck_sound {p : PowerPolynomial7} (hp : p.nonnegativeCheck=true)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : 0≤p.eval t := by
  have hq : 0≤p.b0 ∧ 0≤p.b1 ∧ 0≤p.b2 ∧ 0≤p.b3 ∧ 0≤p.b4 ∧ 0≤p.b5 ∧ 0≤p.b6 ∧ 0≤p.b7 := of_decide_eq_true hp
  rcases hq with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  have h0' : (0:ℝ)≤p.b0 := by exact_mod_cast h0
  have h1' : (0:ℝ)≤p.b1 := by exact_mod_cast h1
  have h2' : (0:ℝ)≤p.b2 := by exact_mod_cast h2
  have h3' : (0:ℝ)≤p.b3 := by exact_mod_cast h3
  have h4' : (0:ℝ)≤p.b4 := by exact_mod_cast h4
  have h5' : (0:ℝ)≤p.b5 := by exact_mod_cast h5
  have h6' : (0:ℝ)≤p.b6 := by exact_mod_cast h6
  have h7' : (0:ℝ)≤p.b7 := by exact_mod_cast h7
  have ht0 : 0≤t := ht.1
  have ht1 : 0≤1-t := sub_nonneg.mpr ht.2
  rw [bernstein_identity]
  positivity
end PowerPolynomial7
namespace RationalPolynomial
def fixed7 (p : RationalPolynomial) : PowerPolynomial7 := ⟨p[0]?.getD 0,p[1]?.getD 0,p[2]?.getD 0,p[3]?.getD 0,p[4]?.getD 0,p[5]?.getD 0,p[6]?.getD 0,p[7]?.getD 0⟩
 theorem eval_take_drop (p : RationalPolynomial) (n : ℕ) (t : ℝ) :
    p.eval t=eval (p.take n) t+t^n*eval (p.drop n) t := by
  induction n generalizing p with
  | zero => simp [eval]
  | succ n ih =>
    cases p with
    | nil => simp [eval]
    | cons a p => simp only [List.take_succ_cons,List.drop_succ_cons,eval,ih p]; ring
 theorem fixed7_eval (p : RationalPolynomial) (t : ℝ) : (fixed7 p).eval t=eval (p.take 8) t := by
  unfold fixed7 PowerPolynomial7.eval
  rcases p with _ | ⟨a0,p⟩
  · simp [eval]
  rcases p with _ | ⟨a1,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a2,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a3,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a4,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a5,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a6,p⟩
  · simp [eval] <;> ring
  rcases p with _ | ⟨a7,p⟩
  · simp [eval] <;> ring
  simp [eval]
  <;> ring
def fixed7Check (p : RationalPolynomial) : Bool :=
  (p.drop 8).all (fun a => decide (a=0)) && (fixed7 p).nonnegativeCheck
 theorem fixed7Check_sound {p : RationalPolynomial} (hc : fixed7Check p=true)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : 0≤p.eval t := by
  have h : (p.drop 8).all (fun a => decide (a=0))=true ∧ (fixed7 p).nonnegativeCheck=true := by
    simpa only [fixed7Check,Bool.and_eq_true] using hc
  have hz := eval_eq_zero h.1 t
  have hp := PowerPolynomial7.nonnegativeCheck_sound h.2 ht
  rw [fixed7_eval] at hp
  rw [eval_take_drop p 8 t,hz]
  simpa using hp
end RationalPolynomial
end OptimalG.Certificates
