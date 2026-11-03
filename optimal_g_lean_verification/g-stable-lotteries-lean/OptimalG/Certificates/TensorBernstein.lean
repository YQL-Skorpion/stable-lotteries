import OptimalG.Certificates.RationalPolynomial

/-! Exact tensor Bernstein proposals. The sign checker only certifies the
displayed polynomial; every use also proves its equality to the target by
ring normalization. No proposal-generation algorithm is trusted. -/
namespace OptimalG.Certificates
open Set

structure TensorBernsteinTerm3 where
  coefficient : ℚ
  x : ℕ
  xc : ℕ
  y : ℕ
  yc : ℕ
  z : ℕ
  zc : ℕ
  deriving Repr, DecidableEq

namespace TensorBernsteinTerm3

noncomputable def eval (t : TensorBernsteinTerm3) (x y z : ℝ) : ℝ :=
  (t.coefficient:ℝ)*x^t.x*(1-x)^t.xc*y^t.y*(1-y)^t.yc*z^t.z*(1-z)^t.zc

theorem eval_nonneg {t : TensorBernsteinTerm3} (hc : 0≤t.coefficient)
    {x y z : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) :
    0≤t.eval x y z := by
  have hc' : (0:ℝ)≤t.coefficient := by exact_mod_cast hc
  have hx0 := hx.1
  have hy0 := hy.1
  have hz0 := hz.1
  have hxc : 0≤1-x := sub_nonneg.mpr hx.2
  have hyc : 0≤1-y := sub_nonneg.mpr hy.2
  have hzc : 0≤1-z := sub_nonneg.mpr hz.2
  dsimp [eval]
  positivity

end TensorBernsteinTerm3

abbrev TensorBernstein3 := List TensorBernsteinTerm3

namespace TensorBernstein3

noncomputable def eval (ts : TensorBernstein3) (x y z : ℝ) : ℝ :=
  (ts.map (fun t => t.eval x y z)).sum

def check (ts : TensorBernstein3) : Bool := ts.all (fun t => decide (0≤t.coefficient))

theorem check_sound {ts : TensorBernstein3} (hc : ts.check=true)
    {x y z : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) (hz : z∈Icc (0:ℝ) 1) :
    0≤ts.eval x y z := by
  apply List.sum_nonneg
  intro a ha
  rcases List.mem_map.mp ha with ⟨t,ht,rfl⟩
  exact t.eval_nonneg (of_decide_eq_true (List.all_eq_true.mp hc t ht)) hx hy hz

end TensorBernstein3

theorem normalized_coordinate_mem {lo hi x : ℝ} (hwidth : lo<hi) (hx : x∈Icc lo hi) :
    (x-lo)/(hi-lo)∈Icc (0:ℝ) 1 := by
  have hd : 0<hi-lo := sub_pos.mpr hwidth
  refine ⟨div_nonneg (sub_nonneg.mpr hx.1) hd.le,?_⟩
  apply (div_le_one hd).mpr
  linarith only [hx.2]

end OptimalG.Certificates
