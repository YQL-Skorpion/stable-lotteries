import OptimalG.Certificates.ReferenceProfileBounds

/-! An exact coefficient hull handles tight zero endpoints without adding a
rounding allowance to the advertised real interval. -/
namespace OptimalG.Certificates
open Set
namespace RationalPolynomial

def coefficientNorm : RationalPolynomial → ℚ
  | [] => 0
  | a::p => |a|+coefficientNorm p

theorem abs_eval_le_coefficientNorm (p : RationalPolynomial) {t : ℝ} (ht : |t|≤1) :
    |eval p t|≤(coefficientNorm p:ℝ) := by
  induction p with
  | nil => simp [eval,coefficientNorm]
  | cons a p ih =>
    have hm := mul_le_mul ht ih (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    calc |eval (a::p) t|≤|(a:ℝ)|+|t| * |eval p t| := by
           simpa only [eval,abs_mul] using abs_add_le (a:ℝ) (t*eval p t)
         _≤|(a:ℝ)|+(coefficientNorm p:ℝ) := by simpa only [one_mul] using add_le_add_right hm _
         _=(coefficientNorm (a::p):ℝ) := by simp [coefficientNorm]

def coefficientHull (p : RationalPolynomial) : RatInterval :=
  match p with
  | [] => ⟨0,0⟩
  | a::p => ⟨a-coefficientNorm p,a+coefficientNorm p⟩

theorem coefficientHull_contains (p : RationalPolynomial) {t : ℝ} (ht : |t|≤1) :
    p.coefficientHull.Contains (eval p t) := by
  cases p with
  | nil => simp [coefficientHull,eval,RatInterval.Contains]
  | cons a p =>
    have hm := mul_le_mul ht (abs_eval_le_coefficientNorm p ht)
      (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hh : |t*eval p t|≤(coefficientNorm p:ℝ) := by simpa only [abs_mul,one_mul] using hm
    have hb := abs_le.mp hh
    simp only [coefficientHull,RatInterval.Contains,eval,Rat.cast_sub,Rat.cast_add]
    constructor <;> linarith

end RationalPolynomial

def exactCenteredPolynomialCheck (s : ℕ) (p : RationalPolynomial) (lo hi : ℚ)
    (out : IntegerInterval) : Bool :=
  let b := (p.compose [(lo+hi)/2,(hi-lo)/2]).coefficientHull
  IntegerInterval.constCheck s b.lo out && IntegerInterval.constCheck s b.hi out

theorem exactCenteredPolynomialCheck_sound {s : ℕ} (p : RationalPolynomial)
    (lo hi : ℚ) (out : IntegerInterval)
    (hc : exactCenteredPolynomialCheck s p lo hi out=true) (horder : lo<hi)
    {x : ℝ} (hx : x∈Icc (lo:ℝ) hi) : out.Contains s (p.eval x) := by
  let t := (2*x-(lo:ℝ)-hi)/((hi:ℝ)-lo)
  have hd : (0:ℝ)<(hi:ℝ)-lo := by exact_mod_cast sub_pos.mpr horder
  have hdn : (hi:ℝ)-(lo:ℝ)≠0 := ne_of_gt hd
  have ht : |t|≤1 := by
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hx.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hx.2]
  have he : ((lo:ℝ)+hi)/2+t*(((hi:ℝ)-lo)/2)=x := by
    dsimp [t]
    field_simp [hdn]
    ring
  have hp := RationalPolynomial.coefficientHull_contains
    (p.compose [(lo+hi)/2,(hi-lo)/2]) ht
  simp only [RationalPolynomial.eval_compose,RationalPolynomial.eval,
    Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat,mul_zero,add_zero,he] at hp
  obtain ⟨hl,hu⟩ := Bool.and_eq_true_iff.mp hc
  have hL := IntegerInterval.constCheck_sound hl
  have hU := IntegerInterval.constCheck_sound hu
  exact ⟨hL.1.trans (mul_le_mul_of_nonneg_left hp.1 (Nat.cast_nonneg s)),
    (mul_le_mul_of_nonneg_left hp.2 (Nat.cast_nonneg s)).trans hU.2⟩

def profilePolynomialCheck (s k : ℕ) (p : RationalPolynomial) (lo hi : ℚ)
    (out : IntegerInterval) : Bool :=
  centeredPolynomialCheck s k p lo hi out || exactCenteredPolynomialCheck s p lo hi out

theorem profilePolynomialCheck_sound {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (p : RationalPolynomial) (lo hi : ℚ) (out : IntegerInterval)
    (hc : profilePolynomialCheck s k p lo hi out=true) (horder : lo<hi)
    {x : ℝ} (hx : x∈Icc (lo:ℝ) hi) : out.Contains s (p.eval x) := by
  rcases Bool.or_eq_true_iff.mp hc with h | h
  · exact centeredPolynomialCheck_sound hs hk p lo hi out h horder hx
  · exact exactCenteredPolynomialCheck_sound p lo hi out h horder hx

end OptimalG.Certificates
