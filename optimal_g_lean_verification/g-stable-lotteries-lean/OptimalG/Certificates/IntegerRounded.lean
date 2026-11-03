import OptimalG.Certificates.IntegerInterval

/-! Deterministic fixed-denominator arithmetic.  Division is used only with
positive integer denominators.  Its results pass the already-proved integer
proposal checker, including the reversed inequalities for negative inverses. -/
namespace OptimalG.Certificates.IntegerInterval

def ceilDiv (a b : ℤ) : ℤ := -((-a)/b)

theorem floor_mul_le (a : ℤ) {b : ℤ} (hb : 0<b) : (a/b)*b≤a :=
  Int.ediv_mul_le a (ne_of_gt hb)

theorem le_ceil_mul (a : ℤ) {b : ℤ} (hb : 0<b) : a≤ceilDiv a b*b := by
  have h := floor_mul_le (-a) hb
  dsimp [ceilDiv]
  nlinarith only [h]

def pointRounded (s : ℕ) (q : ℚ) : IntegerInterval :=
  ⟨((s:ℤ)*q.num)/(q.den:ℤ),ceilDiv ((s:ℤ)*q.num) q.den⟩
def negRounded (a : IntegerInterval) : IntegerInterval := ⟨-a.hi,-a.lo⟩
def addRounded (a b : IntegerInterval) : IntegerInterval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def mulRounded (s : ℕ) (a b : IntegerInterval) : IntegerInterval :=
  ⟨mulLo a b/(s:ℤ),ceilDiv (mulHi a b) s⟩

def invRounded (s : ℕ) (a : IntegerInterval) : Option IntegerInterval :=
  if 0<a.lo ∧ 0<a.hi then some ⟨(s:ℤ)^2/a.hi,ceilDiv ((s:ℤ)^2) a.lo⟩
  else if a.lo<0 ∧ a.hi<0 then
    some ⟨-ceilDiv ((s:ℤ)^2) (-a.hi),-((s:ℤ)^2/(-a.lo))⟩
  else none

theorem pointRounded_checked (s : ℕ) (q : ℚ) : constCheck s q (pointRounded s q)=true := by
  have hd : (0:ℤ)<q.den := by exact_mod_cast q.den_pos
  simpa only [constCheck,pointRounded,decide_eq_true_eq] using
    And.intro (floor_mul_le ((s:ℤ)*q.num) hd) (le_ceil_mul ((s:ℤ)*q.num) hd)

theorem negRounded_checked (a : IntegerInterval) : negCheck a a.negRounded=true := by
  simp [negCheck,negRounded]

theorem addRounded_checked (a b : IntegerInterval) : addCheck a b (a.addRounded b)=true := by
  simp [addCheck,addRounded]

theorem mulRounded_checked {s : ℕ} (hs : 0<s) (a b : IntegerInterval) :
    mulCheck s a b (mulRounded s a b)=true := by
  have hs' : (0:ℤ)<s := by exact_mod_cast hs
  have hl := floor_mul_le (mulLo a b) hs'
  have hu := le_ceil_mul (mulHi a b) hs'
  simpa only [mulCheck,mulRounded,decide_eq_true_eq,mul_comm] using And.intro hl hu

theorem invRounded_checked {s : ℕ} {a out : IntegerInterval}
    (hc : invRounded s a=some out) : invCheck s a out=true := by
  unfold invRounded at hc
  split_ifs at hc with hp hn
  · have ho : out=⟨(s:ℤ)^2/a.hi,ceilDiv ((s:ℤ)^2) a.lo⟩ := (Option.some.inj hc).symm
    subst out
    rw [invCheck,if_pos hp.1]
    simpa only [decide_eq_true_eq] using And.intro (floor_mul_le _ hp.2) (le_ceil_mul _ hp.1)
  · have ho : out=⟨-ceilDiv ((s:ℤ)^2) (-a.hi),-((s:ℤ)^2/(-a.lo))⟩ :=
      (Option.some.inj hc).symm
    subst out
    rw [invCheck,if_neg (not_lt.mpr hn.1.le),if_pos hn.2]
    simp only [decide_eq_true_eq]
    have hl := le_ceil_mul ((s:ℤ)^2) (neg_pos.mpr hn.2)
    have hu := floor_mul_le ((s:ℤ)^2) (neg_pos.mpr hn.1)
    constructor <;> nlinarith only [hl,hu]

theorem pointRounded_contains (s : ℕ) (q : ℚ) : (pointRounded s q).Contains s (q:ℝ) :=
  constCheck_sound (pointRounded_checked s q)

theorem negRounded_contains {s : ℕ} {a : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) : a.negRounded.Contains s (-x) :=
  negCheck_sound hx (negRounded_checked a)

theorem addRounded_contains {s : ℕ} {a b : IntegerInterval} {x y : ℝ}
    (hx : a.Contains s x) (hy : b.Contains s y) : (a.addRounded b).Contains s (x+y) :=
  addCheck_sound hx hy (addRounded_checked a b)

theorem mulRounded_contains {s : ℕ} (hs : 0<s) {a b : IntegerInterval} {x y : ℝ}
    (hx : a.Contains s x) (hy : b.Contains s y) : (mulRounded s a b).Contains s (x*y) :=
  mulCheck_sound hs hx hy (mulRounded_checked hs a b)

theorem invRounded_contains {s : ℕ} (hs : 0<s) {a b : IntegerInterval} {x : ℝ}
    (hx : a.Contains s x) (hc : invRounded s a=some b) : b.Contains s x⁻¹ :=
  invCheck_sound hs hx (invRounded_checked hc)

end OptimalG.Certificates.IntegerInterval
