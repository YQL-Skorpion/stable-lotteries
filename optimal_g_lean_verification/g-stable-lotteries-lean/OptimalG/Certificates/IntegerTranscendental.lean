import OptimalG.Certificates.IntegerExpression
import OptimalG.Certificates.ExpressionAlgebra
import OptimalG.Certificates.Transcendental

/-! Polynomial exponential enclosures evaluated with fixed-denominator integer
arithmetic. The remainder is the proved Mathlib exponential bound. -/
namespace OptimalG.Certificates
open scoped BigOperators
namespace RatExpr

def powerExpr {n : ℕ} (e : RatExpr n) : ℕ→RatExpr n
  | 0 => 1
  | k+1 => powerExpr e k*e

theorem powerExpr_eval {n : ℕ} (e : RatExpr n) (k : ℕ) (x : Fin n→ℝ) :
    (e.powerExpr k).eval x=(e.eval x)^k := by
  induction k with
  | zero => change ((1:ℚ):ℝ)=1; norm_num
  | succ k ih => simp only [powerExpr,eval_mulNotation,ih,pow_succ]

def expTaylorExpr {n : ℕ} (e : RatExpr n) : ℕ→RatExpr n
  | 0 => 0
  | k+1 => expTaylorExpr e k+.const (1/(k.factorial:ℚ))*e.powerExpr k

theorem expTaylorExpr_eval {n : ℕ} (e : RatExpr n) (k : ℕ) (x : Fin n→ℝ) :
    (e.expTaylorExpr k).eval x=∑ i∈Finset.range k,(e.eval x)^i/(i.factorial:ℝ) := by
  induction k with
  | zero => change ((0:ℚ):ℝ)=_; simp
  | succ k ih =>
    simp only [expTaylorExpr,eval_addNotation,eval_mulNotation,powerExpr_eval,eval,
      Rat.cast_div,Rat.cast_one,Rat.cast_natCast,Finset.sum_range_succ,ih]
    ring

def expUpperExpr {n : ℕ} (e : RatExpr n) (k : ℕ) : RatExpr n :=
  e.expTaylorExpr k+.const (((k:ℚ)+1)/((k.factorial:ℚ)*k))*e.powerExpr k

theorem expUpperExpr_eval {n : ℕ} (e : RatExpr n) (k : ℕ) (x : Fin n→ℝ) :
    (e.expUpperExpr k).eval x=(∑ i∈Finset.range k,(e.eval x)^i/(i.factorial:ℝ))+
      (e.eval x)^k*(k+1)/((k.factorial:ℝ)*k) := by
  simp only [expUpperExpr,eval_addNotation,eval_mulNotation,powerExpr_eval,
    expTaylorExpr_eval,eval,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_one,Rat.cast_natCast]
  ring

end RatExpr
namespace IntegerInterval

def rescale (k : ℕ) (a : IntegerInterval) : IntegerInterval :=
  ⟨(k:ℤ)*a.lo,(k:ℤ)*a.hi⟩

theorem rescale_contains_iff {k : ℕ} (hk : 0<k) (s : ℕ) (a : IntegerInterval) (x : ℝ) :
    (a.rescale k).Contains (k*s) x↔a.Contains s x := by
  have hk' : (0:ℝ)<k := by exact_mod_cast hk
  simp only [rescale,Contains,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,mul_assoc]
  rw [mul_le_mul_iff_right₀ hk',mul_le_mul_iff_right₀ hk']

def expCheck (s : ℕ) (n : ℕ) (a out : IntegerInterval) : Bool :=
  decide (0<n ∧ 0≤a.lo ∧ a.hi≤(s:ℤ)) &&
    (match (RatExpr.expTaylorExpr (.var (0:Fin 1)) n).integerInterval s (fun _ => a),
      (RatExpr.expUpperExpr (.var (0:Fin 1)) n).integerInterval s (fun _ => a) with
    | some lo,some hi => decide (out.lo≤lo.lo ∧ hi.hi≤out.hi)
    | _,_ => false)

theorem expCheck_sound {s n : ℕ} (hs : 0<s) {a out : IntegerInterval}
    (hc : expCheck s n a out=true) {x : ℝ} (hx : a.Contains s x) :
    out.Contains s (Real.exp x) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hdom : 0<n ∧ 0≤a.lo ∧ a.hi≤(s:ℤ) := of_decide_eq_true hh.1
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hal : (0:ℝ)≤a.lo := by exact_mod_cast hdom.2.1
  have hah : (a.hi:ℝ)≤s := by exact_mod_cast hdom.2.2
  have hx0 : 0≤x := by dsimp [Contains] at hx; nlinarith [hx.1]
  have hx1 : x≤1 := by dsimp [Contains] at hx; nlinarith [hx.2]
  have hh := hh.2
  cases h0 : (RatExpr.expTaylorExpr (.var (0:Fin 1)) n).integerInterval s (fun _ => a) with
  | none => simp only [h0,Bool.false_eq_true] at hh
  | some lo =>
    cases h1 : (RatExpr.expUpperExpr (.var (0:Fin 1)) n).integerInterval s (fun _ => a) with
    | none => simp only [h0,h1,Bool.false_eq_true] at hh
    | some hi =>
      have hout : out.lo≤lo.lo ∧ hi.hi≤out.hi := by
        simpa only [h0,h1,decide_eq_true_eq] using hh
      have hlo := RatExpr.integerInterval_sound hs _ (fun _ => x) (fun _ => hx) _ h0
      have hhi := RatExpr.integerInterval_sound hs _ (fun _ => x) (fun _ => hx) _ h1
      simp only [RatExpr.expTaylorExpr_eval,RatExpr.expUpperExpr_eval,RatExpr.eval] at hlo hhi
      have hle := Real.sum_le_exp_of_nonneg hx0 n
      have hge := Real.exp_bound' hx0 hx1 hdom.1
      have houtlo : (out.lo:ℝ)≤lo.lo := by exact_mod_cast hout.1
      have houthi : (hi.hi:ℝ)≤out.hi := by exact_mod_cast hout.2
      constructor
      · exact houtlo.trans (hlo.1.trans (mul_le_mul_of_nonneg_left hle hs'.le))
      · exact (mul_le_mul_of_nonneg_left hge hs'.le).trans (hhi.2.trans houthi)

/-- Higher internal precision may establish a coarser advertised enclosure
without modifying the reference data or trusting a rounded transcendental. -/
def expRefinedCheck (s k n : ℕ) (a out : IntegerInterval) : Bool :=
  expCheck (k*s) n (a.rescale k) (out.rescale k)

theorem expRefinedCheck_sound {s k n : ℕ} (hs : 0<s) (hk : 0<k)
    {a out : IntegerInterval} (hc : expRefinedCheck s k n a out=true)
    {x : ℝ} (hx : a.Contains s x) : out.Contains s (Real.exp x) := by
  exact (rescale_contains_iff hk s out _).mp
    (expCheck_sound (Nat.mul_pos hk hs) hc ((rescale_contains_iff hk s a x).mpr hx))

end IntegerInterval
end OptimalG.Certificates
