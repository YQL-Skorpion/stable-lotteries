import OptimalG.Certificates.IntegerExpression

/-! Existing exact rational box partitions with a fixed-denominator integer
arithmetic leaf checker. Splits retain their original real coverage semantics. -/
namespace OptimalG.Certificates
namespace IntegerInterval

def fromRat (s : ℕ) (a : RatInterval) : IntegerInterval :=
  ⟨(pointRounded s a.lo).lo,(pointRounded s a.hi).hi⟩

theorem fromRat_contains {s : ℕ} (hs : 0<s) {a : RatInterval} {x : ℝ}
    (hx : a.Contains x) : (fromRat s a).Contains s x := by
  have hs' : (0:ℝ)≤s := by positivity
  have hl := (pointRounded_contains s a.lo).1
  have hu := (pointRounded_contains s a.hi).2
  exact ⟨hl.trans (mul_le_mul_of_nonneg_left hx.1 hs'),
    (mul_le_mul_of_nonneg_left hx.2 hs').trans hu⟩

end IntegerInterval
namespace BoxCertificate
variable {n : ℕ}

def checkWith (leaf : (Fin n→RatInterval)→Bool) (box : Fin n→RatInterval) : BoxCertificate n→Bool
  | .leaf => leaf box
  | .split i m left right =>
    checkWith leaf (leftBox box i m) left && checkWith leaf (rightBox box i m) right

/-- A generic predicate lets stronger leaf checkers reuse the same coverage
proof without any change to the meaning of the input box. -/
theorem checkWith_sound (leaf : (Fin n→RatInterval)→Bool) (P : (Fin n→ℝ)→Prop)
    (hLeaf : ∀ box,leaf box=true→∀ x,(∀ i,(box i).Contains (x i))→P x)
    (t : BoxCertificate n) : ∀ box,t.checkWith leaf box=true→∀ x,
      (∀ i,(box i).Contains (x i))→P x := by
  induction t with
  | leaf => exact hLeaf
  | split i m left right ihl ihr =>
    intro box hc x hx
    have hh := Bool.and_eq_true_iff.mp hc
    by_cases hm : x i≤(m:ℝ)
    · apply ihl (leftBox box i m) hh.1 x
      intro j
      by_cases hj : j=i
      · subst j
        simpa [leftBox,RatInterval.Contains] using And.intro (hx i).1 hm
      · simpa [leftBox,Function.update_of_ne hj] using hx j
    · apply ihr (rightBox box i m) hh.2 x
      intro j
      by_cases hj : j=i
      · subst j
        simpa [rightBox,RatInterval.Contains] using And.intro (le_of_not_ge hm) (hx i).2
      · simpa [rightBox,Function.update_of_ne hj] using hx j

def integerLowerCheck (s : ℕ) (e : RatExpr n) (box : Fin n→RatInterval) (bound : ℤ)
    (t : BoxCertificate n) : Bool :=
  t.checkWith (fun b => e.integerLowerCheck s (fun i => IntegerInterval.fromRat s (b i)) bound) box

theorem integerLowerCheck_sound {s : ℕ} (hs : 0<s) (e : RatExpr n)
    (box : Fin n→RatInterval) (bound : ℤ) (t : BoxCertificate n)
    (hc : t.integerLowerCheck s e box bound=true) (x : Fin n→ℝ)
    (hx : ∀ i,(box i).Contains (x i)) : (bound:ℝ)/(s:ℝ)<e.eval x := by
  apply checkWith_sound _ (fun x => (bound:ℝ)/(s:ℝ)<e.eval x) ?_ t box hc x hx
  intro b hb y hy
  exact RatExpr.integerLowerCheck_sound hs e _ bound hb y
    (fun i => IntegerInterval.fromRat_contains hs (hy i))

end BoxCertificate
end OptimalG.Certificates
