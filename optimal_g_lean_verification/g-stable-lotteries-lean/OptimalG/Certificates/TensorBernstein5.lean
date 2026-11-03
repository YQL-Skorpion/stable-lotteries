import OptimalG.Certificates.TensorBernstein

/-! Five-coordinate tensor certificates for the diagonal slope bands. -/
namespace OptimalG.Certificates
open Set

structure TensorBernsteinTerm5 where
  coefficient : ℚ
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

namespace TensorBernsteinTerm5
noncomputable def eval (t : TensorBernsteinTerm5) (a b c d e : ℝ) : ℝ :=
  (t.coefficient:ℝ)*a^t.a*(1-a)^t.ac*b^t.b*(1-b)^t.bc*c^t.c*(1-c)^t.cc*
    d^t.d*(1-d)^t.dc*e^t.e*(1-e)^t.ec

theorem eval_nonneg {t : TensorBernsteinTerm5} (hc : 0≤t.coefficient)
    {a b c d e : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hcc : c∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1) (he : e∈Icc (0:ℝ) 1) :
    0≤t.eval a b c d e := by
  have hq : (0:ℝ)≤t.coefficient := by exact_mod_cast hc
  have ha0 := ha.1; have hb0 := hb.1; have hc0 := hcc.1; have hd0 := hd.1; have he0 := he.1
  have ha1 : 0≤1-a := sub_nonneg.mpr ha.2
  have hb1 : 0≤1-b := sub_nonneg.mpr hb.2
  have hc1 : 0≤1-c := sub_nonneg.mpr hcc.2
  have hd1 : 0≤1-d := sub_nonneg.mpr hd.2
  have he1 : 0≤1-e := sub_nonneg.mpr he.2
  dsimp [eval]
  positivity
end TensorBernsteinTerm5

abbrev TensorBernstein5 := List TensorBernsteinTerm5
namespace TensorBernstein5
noncomputable def eval (ts : TensorBernstein5) (a b c d e : ℝ) : ℝ :=
  (ts.map (fun t=>t.eval a b c d e)).sum

def check (ts : TensorBernstein5) : Bool := ts.all (fun t=>decide (0≤t.coefficient))

theorem check_sound {ts : TensorBernstein5} (hc : ts.check=true)
    {a b c d e : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hcc : c∈Icc (0:ℝ) 1) (hd : d∈Icc (0:ℝ) 1) (he : e∈Icc (0:ℝ) 1) :
    0≤ts.eval a b c d e := by
  apply List.sum_nonneg
  intro q hq
  rcases List.mem_map.mp hq with ⟨t,ht,rfl⟩
  exact t.eval_nonneg (of_decide_eq_true (List.all_eq_true.mp hc t ht)) ha hb hcc hd he
end TensorBernstein5
end OptimalG.Certificates
