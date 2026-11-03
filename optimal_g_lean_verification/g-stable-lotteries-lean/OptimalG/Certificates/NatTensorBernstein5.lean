import OptimalG.Certificates.TensorBernstein5

/-! Tensor Bernstein certificates with natural coefficients and one external
positive denominator. Nonnegativity is structural; no large rational sign
computation is needed. Each application must still prove its exact polynomial
identity in the kernel. -/
namespace OptimalG.Certificates
open Set

structure NatTensorBernsteinTerm5 where
  coefficient : ℕ
  a : ℕ
  ac : ℕ
  b : ℕ
  bc : ℕ
  c : ℕ
  cc : ℕ
  d : ℕ
  dc : ℕ
  e : ℕ
  ec : ℕ
  deriving Repr, DecidableEq

namespace NatTensorBernsteinTerm5
noncomputable def eval (t : NatTensorBernsteinTerm5) (a b c d e : ℝ) : ℝ :=
  (t.coefficient:ℝ)*a^t.a*(1-a)^t.ac*b^t.b*(1-b)^t.bc*c^t.c*(1-c)^t.cc*
    d^t.d*(1-d)^t.dc*e^t.e*(1-e)^t.ec

theorem eval_nonneg (t : NatTensorBernsteinTerm5)
    {a b c d e : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hc : c∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1) (he : e∈Icc (0:ℝ) 1) :
    0≤t.eval a b c d e := by
  have ha0 := ha.1; have hb0 := hb.1; have hc0 := hc.1
  have hd0 := hd.1; have he0 := he.1
  have ha1 : 0≤1-a := sub_nonneg.mpr ha.2
  have hb1 : 0≤1-b := sub_nonneg.mpr hb.2
  have hc1 : 0≤1-c := sub_nonneg.mpr hc.2
  have hd1 : 0≤1-d := sub_nonneg.mpr hd.2
  have he1 : 0≤1-e := sub_nonneg.mpr he.2
  dsimp [eval]
  positivity
end NatTensorBernsteinTerm5

abbrev NatTensorBernstein5 := List NatTensorBernsteinTerm5
namespace NatTensorBernstein5
noncomputable def eval (ts : NatTensorBernstein5) (a b c d e : ℝ) : ℝ :=
  (ts.map (fun t=>t.eval a b c d e)).sum

theorem eval_nonneg (ts : NatTensorBernstein5)
    {a b c d e : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hc : c∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1) (he : e∈Icc (0:ℝ) 1) :
    0≤ts.eval a b c d e := by
  apply List.sum_nonneg
  intro q hq
  rcases List.mem_map.mp hq with ⟨t,ht,rfl⟩
  exact t.eval_nonneg ha hb hc hd he
end NatTensorBernstein5
end OptimalG.Certificates
