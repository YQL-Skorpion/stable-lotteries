import OptimalG.UniversalLPFastCheck

/-! A separate exact dual checker whose accumulation takes place in integers.
The certificate proposes one positive common scale. Every rational input or
product is related to its proposed integer by an integer cross multiplication;
all residual normalization and scalar summation then avoid rational gcds. -/
namespace OptimalG.UniversalLP

abbrev IntegerTerms := List (ℕ × ℤ)

def integerCoeff (ts : IntegerTerms) (j : Variables) : ℤ :=
  (ts.map fun t => if t.1 = j.val then t.2 else 0).sum

@[simp] theorem integerCoeff_nil (j : Variables) : integerCoeff [] j = 0 := by
  simp [integerCoeff]
@[simp] theorem integerCoeff_cons (t : ℕ × ℤ) (ts : IntegerTerms) (j : Variables) :
    integerCoeff (t :: ts) j = (if t.1 = j.val then t.2 else 0) + integerCoeff ts j := by
  simp [integerCoeff]
@[simp] theorem integerCoeff_append (a b : IntegerTerms) (j : Variables) :
    integerCoeff (a ++ b) j = integerCoeff a j + integerCoeff b j := by
  simp [integerCoeff]

def insertIntegerTerm (t : ℕ × ℤ) : IntegerTerms → IntegerTerms
  | [] => if t.2 = 0 then [] else [t]
  | a :: ts =>
      if t.2 = 0 then a :: ts
      else if t.1 < a.1 then t :: a :: ts
      else if t.1 = a.1 then
        if t.2 + a.2 = 0 then ts else (t.1,t.2+a.2) :: ts
      else a :: insertIntegerTerm t ts

def normalizeIntegerTerms (ts : IntegerTerms) : IntegerTerms := ts.foldr insertIntegerTerm []

@[simp] theorem integerCoeff_insert (t : ℕ × ℤ) (ts : IntegerTerms) (j : Variables) :
    integerCoeff (insertIntegerTerm t ts) j =
      (if t.1 = j.val then t.2 else 0) + integerCoeff ts j := by
  induction ts with
  | nil => by_cases ht : t.2=0 <;> simp [insertIntegerTerm,ht]
  | cons a ts ih =>
      simp only [insertIntegerTerm]
      by_cases ht : t.2=0
      · simp [ht]
      rw [if_neg ht]
      by_cases hlt : t.1<a.1
      · rw [if_pos hlt]
        simp only [integerCoeff_cons]
      rw [if_neg hlt]
      by_cases heq : t.1=a.1
      · rw [if_pos heq]
        by_cases hz : t.2+a.2=0
        · rw [if_pos hz]
          by_cases hj : a.1=j.val
          · simp only [integerCoeff_cons,heq,hj,if_true]
            omega
          · simp [heq,hj]
        · rw [if_neg hz]
          by_cases hj : a.1=j.val <;> simp [heq,hj] <;> omega
      · rw [if_neg heq]
        simp only [integerCoeff_cons,ih]
        omega

@[simp] theorem integerCoeff_normalize (ts : IntegerTerms) (j : Variables) :
    integerCoeff (normalizeIntegerTerms ts) j = integerCoeff ts j := by
  induction ts with
  | nil => simp [normalizeIntegerTerms]
  | cons t ts ih =>
      simp only [normalizeIntegerTerms,List.foldr_cons,integerCoeff_insert,integerCoeff_cons] at *
      rw [ih]

theorem integerCoeff_flatten (tss : List IntegerTerms) (j : Variables) :
    integerCoeff tss.flatten j = (tss.map fun ts => integerCoeff ts j).sum := by
  induction tss with
  | nil => simp
  | cons ts tss ih => simp [ih]

/-- Cross multiplication of a single rational input, with no rational product. -/
def scaledIntegerCheck (scale : ℕ) (q : ℚ) (n : ℤ) : Bool :=
  decide (n * (q.den : ℤ) = (scale : ℤ) * q.num)

/-- Cross multiplication of a product. It deliberately never forms `a*b` as a rational. -/
def scaledProductCheck (scale : ℕ) (a b : ℚ) (n : ℤ) : Bool :=
  if a.num = 0 then decide (n = 0)
  else decide (n * (a.den : ℤ) * (b.den : ℤ) = (scale : ℤ) * a.num * b.num)

theorem scaledIntegerCheck_sound {scale : ℕ} {q : ℚ} {n : ℤ}
    (hc : scaledIntegerCheck scale q n = true) : (n : ℚ) = scale * q := by
  have hh := of_decide_eq_true hc
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have he : (n : ℚ) * q.den = (scale : ℚ) * q.num := by exact_mod_cast hh
  calc
    (n : ℚ) = (scale : ℚ) * ((q.num : ℚ) / q.den) := by
      apply (eq_div_iff hden).2 at he
      simpa [mul_div_assoc] using he
    _ = scale * q := by rw [Rat.num_div_den]

theorem scaledProductCheck_sound {scale : ℕ} {a b : ℚ} {n : ℤ}
    (hc : scaledProductCheck scale a b n = true) : (n : ℚ) = scale * a * b := by
  unfold scaledProductCheck at hc
  split_ifs at hc with hz
  · have hn : n=0 := of_decide_eq_true hc
    rw [Rat.num_eq_zero.mp hz,hn]
    simp
  have hh := of_decide_eq_true hc
  have ha : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hb : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_ne_zero
  have he : (n : ℚ) * a.den * b.den = (scale : ℚ) * a.num * b.num := by
    exact_mod_cast hh
  calc
    (n : ℚ) = (scale : ℚ) * ((a.num : ℚ)/a.den) * ((b.num : ℚ)/b.den) := by
      field_simp
      nlinarith only [he]
    _ = scale * a * b := by rw [Rat.num_div_den,Rat.num_div_den]

/-- Match a complete row, including every sparse index and list length. -/
def scaledTermsCheck (scale : ℕ) (factor : ℚ) : Terms → IntegerTerms → Bool
  | [], [] => true
  | a::as, b::bs => decide (a.1=b.1) && scaledProductCheck scale factor a.2 b.2 &&
      scaledTermsCheck scale factor as bs
  | _, _ => false

theorem scaledTermsCheck_sound {scale : ℕ} {factor : ℚ} {ts : Terms}
    {ns : IntegerTerms} (hc : scaledTermsCheck scale factor ts ns = true) (j : Variables) :
    (integerCoeff ns j : ℚ) = scale * factor * coeff ts j := by
  induction ts generalizing ns with
  | nil => cases ns <;> simp_all [scaledTermsCheck]
  | cons a ts ih =>
      cases ns with
      | nil => simp [scaledTermsCheck] at hc
      | cons b ns =>
          have hh := Bool.and_eq_true_iff.mp hc
          have hh0 := Bool.and_eq_true_iff.mp hh.1
          have hab : a.1=b.1 := of_decide_eq_true hh0.1
          have hb := scaledProductCheck_sound hh0.2
          have htail := ih hh.2
          simp only [integerCoeff_cons,Int.cast_add,coeff_cons]
          rw [htail]
          by_cases hj : a.1=j.val
          · simp only [← hab,hj,if_true]
            rw [hb]
            ring
          · simp [← hab,hj,mul_add]

/-- All arrays are proposed data, with out-of-range entries handled by `get!`.
Every used entry is checked; no length or data-trust assumption is required. -/
structure IntegerDualCertificate where
  scale : ℕ
  objective : IntegerTerms
  weightedRows : Array IntegerTerms
  residual : IntegerTerms
  rhsProducts : Array ℤ
  lowerProducts : Array ℤ
  upperProducts : Array ℤ
  bound : ℤ
  deriving Inhabited

namespace IntegerDualCertificate

def expanded (c : IntegerDualCertificate) (d : DualProposal) : IntegerTerms :=
  c.objective ++ (List.ofFn fun i : Fin d.support.size => c.weightedRows[i.val]!).flatten

def check (c : IntegerDualCertificate) (d : DualProposal) (rows : Array RowTag)
    (terms : Array Terms) (rhs : Array ℚ) (known : ℕ) : Bool :=
  decide (0 < c.scale ∧ known ≤ rows.size ∧ ∀ i, d.rowIndex i < known) &&
  decide (∀ i, d.multiplier i ≤ 0) &&
  scaledTermsCheck c.scale 1 d.objective c.objective &&
  decide (∀ i : Fin d.support.size,
    scaledTermsCheck c.scale (-d.multiplier i) terms[d.rowIndex i]!
      c.weightedRows[i.val]! = true) &&
  decide (normalizeIntegerTerms (c.expanded d) = c.residual) &&
  decide (∀ j, scaledIntegerCheck c.scale (d.remainder j) (integerCoeff c.residual j) = true) &&
  decide (∀ i : Fin d.support.size,
    scaledProductCheck c.scale (d.multiplier i) (d.cachedRhs rhs i) c.rhsProducts[i.val]! = true) &&
  decide (∀ j : Variables,
    scaledProductCheck c.scale (d.remainder j) (lower j) c.lowerProducts[j.val]! = true ∧
    scaledProductCheck c.scale (d.remainder j) (upper j) c.upperProducts[j.val]! = true) &&
  scaledIntegerCheck c.scale d.bound c.bound &&
  decide (c.bound ≤ (∑ i : Fin d.support.size, c.rhsProducts[i.val]!) +
    ∑ j : Variables, min c.lowerProducts[j.val]! c.upperProducts[j.val]!)

theorem coeff_expanded {c : IntegerDualCertificate} {d : DualProposal} {terms : Array Terms}
    (hobj : scaledTermsCheck c.scale 1 d.objective c.objective = true)
    (hrow : ∀ i : Fin d.support.size, scaledTermsCheck c.scale (-d.multiplier i)
      terms[d.rowIndex i]! c.weightedRows[i.val]! = true) (j : Variables) :
    (integerCoeff (c.expanded d) j : ℚ) =
      c.scale * (coeff d.objective j - ∑ i, d.multiplier i * d.cachedMatrix terms i j) := by
  simp only [expanded,integerCoeff_append,integerCoeff_flatten,List.map_ofFn,
    Function.comp_def,List.sum_ofFn,Int.cast_add,Int.cast_sum]
  rw [scaledTermsCheck_sound hobj]
  simp_rw [scaledTermsCheck_sound (hrow _)]
  simp only [DualProposal.cachedMatrix,mul_one,mul_assoc,neg_mul,mul_neg,Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

/-- A successful integer certificate recovers the original exact rational checker. -/
theorem checkCached_of_check {c : IntegerDualCertificate} {d : DualProposal}
    {rows : Array RowTag} {terms : Array Terms} {rhs : Array ℚ} {known : ℕ}
    (hc : c.check d rows terms rhs known = true) :
    d.checkCached rows terms rhs known = true := by
  simp only [check,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hidx,hsign⟩,hobj⟩,hrow⟩,hnorm⟩,hres⟩,hrhs⟩,hbox⟩,hbound⟩,hsum⟩
  have hscale : (0 : ℚ) < c.scale := by exact_mod_cast hidx.1
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hidx.2,?_⟩
  apply decide_eq_true
  refine ⟨hsign,?_,?_⟩
  · intro j
    have he := coeff_expanded hobj hrow j
    have hn := congrArg (fun ts => integerCoeff ts j) hnorm
    rw [integerCoeff_normalize] at hn
    rw [hn,scaledIntegerCheck_sound (hres j)] at he
    have he' := (mul_left_cancel₀ (ne_of_gt hscale) he)
    linarith
  · have he : (c.bound : ℚ) ≤ (∑ i : Fin d.support.size, (c.rhsProducts[i.val]! : ℚ)) +
        ∑ j : Variables, min (c.lowerProducts[j.val]! : ℚ) (c.upperProducts[j.val]! : ℚ) := by
      exact_mod_cast hsum
    rw [scaledIntegerCheck_sound hbound] at he
    simp_rw [scaledProductCheck_sound (hrhs _),
      scaledProductCheck_sound (hbox _).1,scaledProductCheck_sound (hbox _).2] at he
    simp_rw [mul_assoc,← mul_min_of_nonneg _ _ hscale.le] at he
    rw [← Finset.mul_sum,← Finset.mul_sum,← mul_add] at he
    exact (mul_le_mul_iff_right₀ hscale).mp he

end IntegerDualCertificate
end OptimalG.UniversalLP
