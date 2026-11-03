import OptimalG.Certificates.RoundedProgram

/-! Fixed-denominator interval proposals.  All acceptance tests use integer
arithmetic.  Rounding is certified by inequalities, so the generator may use
any directed-rounding implementation without entering the trusted kernel. -/
namespace OptimalG.Certificates

structure IntegerInterval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace IntegerInterval

def toRat (s : ℕ) (a : IntegerInterval) : RatInterval :=
  ⟨(a.lo:ℚ)/s, (a.hi:ℚ)/s⟩

def Contains (s : ℕ) (a : IntegerInterval) (x : ℝ) : Prop :=
  (a.lo:ℝ)≤(s:ℝ)*x ∧ (s:ℝ)*x≤(a.hi:ℝ)

theorem contains_iff {s : ℕ} (hs : 0<s) (a : IntegerInterval) (x : ℝ) :
    a.Contains s x ↔ (a.toRat s).Contains x := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  simp only [Contains,toRat,RatInterval.Contains,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  rw [div_le_iff₀ hs',le_div_iff₀ hs']
  simp only [mul_comm]

theorem positive {s : ℕ} (hs : 0<s) {a : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hl : 0<a.lo) : 0<x := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hl' : (0:ℝ)<a.lo := by exact_mod_cast hl
  exact (mul_pos_iff_of_pos_left hs').mp (hl'.trans_le hx.1)

theorem lower_bound {s : ℕ} (hs : 0<s) {a : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) : (a.lo:ℝ)/(s:ℝ)≤x := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  exact (div_le_iff₀ hs').mpr (by simpa only [mul_comm] using hx.1)

theorem upper_bound {s : ℕ} (hs : 0<s) {a : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) : x≤(a.hi:ℝ)/(s:ℝ) := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  exact (le_div_iff₀ hs').mpr (by simpa only [mul_comm] using hx.2)

def subsetCheck (a b : IntegerInterval) : Bool := decide (b.lo≤a.lo ∧ a.hi≤b.hi)
def negCheck (a out : IntegerInterval) : Bool := decide (out.lo≤-a.hi ∧ -a.lo≤out.hi)
def addCheck (a b out : IntegerInterval) : Bool :=
  decide (out.lo≤a.lo+b.lo ∧ a.hi+b.hi≤out.hi)
def mulLo (a b : IntegerInterval) : ℤ :=
  min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))
def mulHi (a b : IntegerInterval) : ℤ :=
  max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))
def mulCheck (s : ℕ) (a b out : IntegerInterval) : Bool :=
  decide ((s:ℤ)*out.lo≤mulLo a b ∧ mulHi a b≤(s:ℤ)*out.hi)

/-- Negative denominator endpoints reverse both cross-product comparisons. -/
def invCheck (s : ℕ) (a out : IntegerInterval) : Bool :=
  if 0<a.lo then decide (out.lo*a.hi≤(s:ℤ)^2 ∧ (s:ℤ)^2≤out.hi*a.lo)
  else if a.hi<0 then decide ((s:ℤ)^2≤out.lo*a.hi ∧ out.hi*a.lo≤(s:ℤ)^2)
  else false

def constCheck (s : ℕ) (q : ℚ) (out : IntegerInterval) : Bool :=
  decide (out.lo*(q.den:ℤ)≤(s:ℤ)*q.num ∧ (s:ℤ)*q.num≤out.hi*(q.den:ℤ))

theorem subsetCheck_sound {s : ℕ} {a out : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hc : a.subsetCheck out=true) : out.Contains s x := by
  have h : out.lo≤a.lo ∧ a.hi≤out.hi := by simpa [subsetCheck] using hc
  have hl : (out.lo : ℝ) ≤ a.lo := by exact_mod_cast h.1
  have hu : (a.hi : ℝ) ≤ out.hi := by exact_mod_cast h.2
  exact ⟨hl.trans hx.1,hx.2.trans hu⟩

theorem negCheck_sound {s : ℕ} {a out : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hc : a.negCheck out=true) : out.Contains s (-x) := by
  have h : out.lo≤-a.hi ∧ -a.lo≤out.hi := by simpa [negCheck] using hc
  have hl : (out.lo:ℝ)≤-(a.hi:ℝ) := by exact_mod_cast h.1
  have hu : -(a.lo:ℝ)≤(out.hi:ℝ) := by exact_mod_cast h.2
  constructor <;> dsimp [Contains] at hx ⊢ <;> nlinarith [hx.1,hx.2]

theorem addCheck_sound {s : ℕ} {a b out : IntegerInterval} {x y : ℝ}
    (hx : a.Contains s x) (hy : b.Contains s y) (hc : a.addCheck b out=true) :
    out.Contains s (x+y) := by
  have h : out.lo≤a.lo+b.lo ∧ a.hi+b.hi≤out.hi := by simpa [addCheck] using hc
  have hl : (out.lo:ℝ)≤(a.lo:ℝ)+(b.lo:ℝ) := by exact_mod_cast h.1
  have hu : (a.hi:ℝ)+(b.hi:ℝ)≤(out.hi:ℝ) := by exact_mod_cast h.2
  constructor <;> dsimp [Contains] at hx hy ⊢ <;> nlinarith [hx.1,hx.2,hy.1,hy.2]

private theorem real_mul_bounds {a b : IntegerInterval} {x y : ℝ}
    (hx : (a.lo:ℝ)≤x ∧ x≤(a.hi:ℝ)) (hy : (b.lo:ℝ)≤y ∧ y≤(b.hi:ℝ)) :
    ((mulLo a b:ℤ):ℝ)≤x*y ∧ x*y≤((mulHi a b:ℤ):ℝ) := by
  let aa : RatInterval := ⟨a.lo,a.hi⟩
  let bb : RatInterval := ⟨b.lo,b.hi⟩
  have ha : aa.Contains x := by simpa [aa,RatInterval.Contains] using hx
  have hb : bb.Contains y := by simpa [bb,RatInterval.Contains] using hy
  have h := RatInterval.mul_contains ha hb
  simpa [aa,bb,RatInterval.mul,RatInterval.Contains,mulLo,mulHi,or_assoc] using h

theorem mulCheck_sound {s : ℕ} (hs : 0<s) {a b out : IntegerInterval} {x y : ℝ}
    (hx : a.Contains s x) (hy : b.Contains s y) (hc : mulCheck s a b out=true) :
    out.Contains s (x*y) := by
  have h : (s:ℤ)*out.lo≤mulLo a b ∧ mulHi a b≤(s:ℤ)*out.hi := by
    simpa [mulCheck] using hc
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hl : (s:ℝ)*(out.lo:ℝ)≤((mulLo a b:ℤ):ℝ) := by exact_mod_cast h.1
  have hu : ((mulHi a b:ℤ):ℝ)≤(s:ℝ)*(out.hi:ℝ) := by exact_mod_cast h.2
  have hm := real_mul_bounds hx hy
  constructor
  · apply (mul_le_mul_iff_right₀ hs').mp
    calc (s:ℝ)*(out.lo:ℝ)≤((mulLo a b:ℤ):ℝ) := hl
         _≤((s:ℝ)*x)*((s:ℝ)*y) := hm.1
         _=(s:ℝ)*((s:ℝ)*(x*y)) := by ring
  · apply (mul_le_mul_iff_right₀ hs').mp
    calc (s:ℝ)*((s:ℝ)*(x*y))=((s:ℝ)*x)*((s:ℝ)*y) := by ring
         _≤((mulHi a b:ℤ):ℝ) := hm.2
         _≤(s:ℝ)*(out.hi:ℝ) := hu

theorem invCheck_sound {s : ℕ} (hs : 0<s) {a out : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hc : invCheck s a out=true) : out.Contains s x⁻¹ := by
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  have hx' := (contains_iff hs a x).mp hx
  simp only [toRat,RatInterval.Contains,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] at hx'
  apply (contains_iff hs out x⁻¹).mpr
  simp only [toRat,RatInterval.Contains,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast]
  unfold invCheck at hc
  split_ifs at hc with hp hn
  · have hp' : (0:ℝ)<a.lo := by exact_mod_cast hp
    have hlo : (0:ℝ)<(a.lo:ℝ)/(s:ℝ) := div_pos hp' hs'
    have hxp : 0<x := hlo.trans_le hx'.1
    have hhi : (0:ℝ)<a.hi := by nlinarith [hx.1,hx.2]
    have h : out.lo*a.hi≤(s:ℤ)^2 ∧ (s:ℤ)^2≤out.hi*a.lo := by simpa using hc
    have hL : (out.lo:ℝ)*(a.hi:ℝ)≤(s:ℝ)^2 := by exact_mod_cast h.1
    have hU : (s:ℝ)^2≤(out.hi:ℝ)*(a.lo:ℝ) := by exact_mod_cast h.2
    constructor
    · calc (out.lo:ℝ)/(s:ℝ)≤(s:ℝ)/(a.hi:ℝ) := by
             apply (div_le_div_iff₀ hs' hhi).mpr
             nlinarith only [hL]
           _=((a.hi:ℝ)/(s:ℝ))⁻¹ := by rw [inv_div]
           _≤x⁻¹ := inv_anti₀ hxp hx'.2
    · calc x⁻¹≤((a.lo:ℝ)/(s:ℝ))⁻¹ := inv_anti₀ hlo hx'.1
           _=(s:ℝ)/(a.lo:ℝ) := by rw [inv_div]
           _≤(out.hi:ℝ)/(s:ℝ) := by
             apply (div_le_div_iff₀ hp' hs').mpr
             nlinarith only [hU]
  · have hn' : (a.hi:ℝ)<0 := by exact_mod_cast hn
    have hhi : (a.hi:ℝ)/(s:ℝ)<0 := div_neg_of_neg_of_pos hn' hs'
    have hxn : x<0 := hx'.2.trans_lt hhi
    have hlo : (a.lo:ℝ)/(s:ℝ)<0 := hx'.1.trans_lt hxn
    have hlo' : (a.lo:ℝ)<0 := by nlinarith [hx.1,hx.2]
    have h : (s:ℤ)^2≤out.lo*a.hi ∧ out.hi*a.lo≤(s:ℤ)^2 := by simpa using hc
    have hL : (s:ℝ)^2≤(out.lo:ℝ)*(a.hi:ℝ) := by exact_mod_cast h.1
    have hU : (out.hi:ℝ)*(a.lo:ℝ)≤(s:ℝ)^2 := by exact_mod_cast h.2
    constructor
    · calc (out.lo:ℝ)/(s:ℝ)≤(s:ℝ)/(a.hi:ℝ) := by
             rw [div_le_iff₀ hs']
             rw [show (s:ℝ)/(a.hi:ℝ)*(s:ℝ)=(s:ℝ)^2/(a.hi:ℝ) by ring]
             exact (le_div_iff_of_neg hn').mpr hL
           _=((a.hi:ℝ)/(s:ℝ))⁻¹ := by rw [inv_div]
           _≤x⁻¹ := (inv_le_inv_of_neg hhi hxn).mpr hx'.2
    · calc x⁻¹≤((a.lo:ℝ)/(s:ℝ))⁻¹ := (inv_le_inv_of_neg hxn hlo).mpr hx'.1
           _=(s:ℝ)/(a.lo:ℝ) := by rw [inv_div]
           _≤(out.hi:ℝ)/(s:ℝ) := by
             rw [le_div_iff₀ hs']
             rw [show (s:ℝ)/(a.lo:ℝ)*(s:ℝ)=(s:ℝ)^2/(a.lo:ℝ) by ring]
             exact (div_le_iff_of_neg hlo').mpr hU

theorem constCheck_sound {s : ℕ} {q : ℚ} {out : IntegerInterval}
    (hc : constCheck s q out=true) : out.Contains s (q:ℝ) := by
  have h : out.lo*(q.den:ℤ)≤(s:ℤ)*q.num ∧ (s:ℤ)*q.num≤out.hi*(q.den:ℤ) := by
    simpa [constCheck] using hc
  have hd : (0:ℝ)<q.den := by exact_mod_cast q.den_pos
  have hq : (q:ℝ)=(q.num:ℝ)/(q.den:ℝ) := by
    conv_lhs => rw [←q.num_div_den]
    norm_cast
  have hl : (out.lo:ℝ)*(q.den:ℝ)≤(s:ℝ)*(q.num:ℝ) := by exact_mod_cast h.1
  have hu : (s:ℝ)*(q.num:ℝ)≤(out.hi:ℝ)*(q.den:ℝ) := by exact_mod_cast h.2
  constructor
  · change (out.lo:ℝ)≤(s:ℝ)*(q:ℝ)
    rw [hq,←mul_div_assoc]
    exact (le_div_iff₀ hd).mpr hl
  · change (s:ℝ)*(q:ℝ)≤(out.hi:ℝ)
    rw [hq,←mul_div_assoc]
    exact (div_le_iff₀ hd).mpr hu

end IntegerInterval
end OptimalG.Certificates
