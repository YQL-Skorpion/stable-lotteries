import OptimalG.Certificates.ReferenceRankTube

/-! Early/late control order tightens the two independently certified rank
intervals before the universal Hessian checker is applied. -/
namespace OptimalG.Certificates

namespace IntegerInterval

def orderedRankR (late : Bool) (r a : IntegerInterval) : IntegerInterval :=
  if late then ⟨max r.lo a.lo,r.hi⟩ else ⟨r.lo,min r.hi a.hi⟩
def orderedRankA (late : Bool) (r a : IntegerInterval) : IntegerInterval :=
  if late then ⟨a.lo,min a.hi r.hi⟩ else ⟨max a.lo r.lo,a.hi⟩

def orderedRanksCheck (late : Bool) (r a targetR targetA : IntegerInterval) : Bool :=
  (orderedRankR late r a).subsetCheck targetR &&
    (orderedRankA late r a).subsetCheck targetA

theorem orderedRanksCheck_sound {s : ℕ} (late : Bool)
    (rawR rawA targetR targetA : IntegerInterval)
    (hc : orderedRanksCheck late rawR rawA targetR targetA=true)
    {r a : ℝ} (hr : rawR.Contains s r) (ha : rawA.Contains s a)
    (horder : if late then a≤r else r≤a) :
    targetR.Contains s r ∧ targetA.Contains s a := by
  obtain ⟨hR,hA⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨subsetCheck_sound ?_ hR,subsetCheck_sound ?_ hA⟩
  · cases late with
    | false =>
      change rawR.lo≤(s:ℝ)*r ∧ (s:ℝ)*r≤(min rawR.hi rawA.hi:ℤ)
      refine ⟨hr.1,?_⟩
      rw [Int.cast_min]
      exact le_min hr.2 ((mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg s)).trans ha.2)
    | true =>
      change (max rawR.lo rawA.lo:ℤ)≤(s:ℝ)*r ∧ (s:ℝ)*r≤rawR.hi
      refine ⟨?_,hr.2⟩
      rw [Int.cast_max]
      exact max_le hr.1 (ha.1.trans (mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg s)))
  · cases late with
    | false =>
      change (max rawA.lo rawR.lo:ℤ)≤(s:ℝ)*a ∧ (s:ℝ)*a≤rawA.hi
      refine ⟨?_,ha.2⟩
      rw [Int.cast_max]
      exact max_le ha.1 (hr.1.trans (mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg s)))
    | true =>
      change rawA.lo≤(s:ℝ)*a ∧ (s:ℝ)*a≤(min rawA.hi rawR.hi:ℤ)
      refine ⟨ha.1,?_⟩
      rw [Int.cast_min]
      exact le_min ha.2 ((mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg s)).trans hr.2)

end IntegerInterval
end OptimalG.Certificates
