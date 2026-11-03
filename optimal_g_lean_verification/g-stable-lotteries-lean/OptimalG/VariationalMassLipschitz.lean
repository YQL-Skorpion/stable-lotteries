import OptimalG.VariationalFeatureSupport
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Uniform geometric regularity of the primitive in the mass coordinate. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem cap_difference (lam S p q : ℝ) (hp : p ≠ 1) (hq : q ≠ 1) :
    cap lam S q-cap lam S p = (q-p)*(lam/2-lam*S/((1-p)*(1-q))) := by
  have hp' : 1-p ≠ 0 := sub_ne_zero.mpr hp.symm
  have hq' : 1-q ≠ 0 := sub_ne_zero.mpr hq.symm
  unfold cap
  field_simp
  ring

theorem Admissible.cap_mass_lipschitz {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    LipschitzOnWith 1 (cap lam d.S) (Icc pLo ell) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro p hp q hq
  have hL0 : 0 ≤ lam := by have hh := hd.1.1; norm_num [lambdaLo] at hh; linarith
  have hL1 : lam ≤ 1 := by have hh := hd.1.2; norm_num [lambdaHi] at hh; linarith
  have hS0 : 0 ≤ d.S := by have hh := hd.slack_lower; linarith
  have hS1 : d.S ≤ 3/100 := by have hh := hd.slack_upper; linarith
  have hpmax : p ≤ 28/100 := hp.2
  have hqmax : q ≤ 28/100 := hq.2
  have hden : (1/2:ℝ) ≤ (1-p)*(1-q) := by
    have hh := mul_le_mul (show (72:ℝ)/100 ≤ 1-p by linarith)
      (show (72:ℝ)/100 ≤ 1-q by linarith) (by norm_num) (by linarith : 0 ≤ 1-p)
    norm_num at hh
    linarith
  have hden0 : 0 < (1-p)*(1-q) := by linarith
  have hLS := mul_le_mul hL1 hS1 hS0 (by norm_num : (0:ℝ) ≤ 1)
  have hfrac : 0 ≤ lam*d.S/((1-p)*(1-q)) ∧ lam*d.S/((1-p)*(1-q)) ≤ 6/100 := by
    constructor
    · exact div_nonneg (mul_nonneg hL0 hS0) hden0.le
    · apply (div_le_iff₀ hden0).mpr
      nlinarith
  have hcoef : |lam/2-lam*d.S/((1-p)*(1-q))| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [Real.dist_eq,Real.dist_eq]
  rw [abs_sub_comm (cap lam d.S p),cap_difference lam d.S p q (by linarith) (by linarith),abs_mul]
  simp only [NNReal.coe_one,one_mul]
  calc
    |q-p| *|lam/2-lam*d.S/((1-p)*(1-q))| ≤ |q-p| *1 := mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)
    _ = |p-q| := by rw [mul_one,abs_sub_comm]

theorem lipschitzOnWith_glue_Icc {f g : ℝ → ℝ} {a b c : ℝ} {K : ℝ≥0}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : LipschitzOnWith K f (Icc a c))
    (hg : LipschitzOnWith K g (Icc c b)) (hfg : f c=g c) :
    LipschitzOnWith K (fun r => if r ≤ c then f r else g r) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
  by_cases hyc : y ≤ c
  · have hxc := hxy.trans hyc
    simp only [hxc,hyc,if_pos]
    exact hf.dist_le_mul x ⟨hx.1,hxc⟩ y ⟨hy.1,hyc⟩
  · by_cases hxc : x ≤ c
    · simp only [hxc,hyc,if_pos,if_neg]
      have hfc := hf.dist_le_mul x ⟨hx.1,hxc⟩ c ⟨hac,le_rfl⟩
      have hgc := hg.dist_le_mul c ⟨le_rfl,hcb⟩ y ⟨(lt_of_not_ge hyc).le,hy.2⟩
      calc
        dist (f x) (g y) ≤ dist (f x) (f c)+dist (f c) (g y) := dist_triangle _ _ _
        _ ≤ K*dist x c+K*dist c y := by rw [hfg]; exact add_le_add (by rwa [hfg] at hfc) hgc
        _ = K*dist x y := by
          rw [Real.dist_eq,Real.dist_eq,Real.dist_eq,
            abs_of_nonpos (sub_nonpos.mpr hxc),abs_of_nonpos (by linarith),abs_of_nonpos (sub_nonpos.mpr hxy)]
          ring
    · simp only [hxc,hyc,if_neg]
      exact hg.dist_le_mul x ⟨(lt_of_not_ge hxc).le,hx.2⟩ y ⟨(lt_of_not_ge hyc).le,hy.2⟩

theorem Admissible.primitive_mass_lipschitz {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    LipschitzOnWith 1 (primitive lam d) (Icc pLo pHi) := by
  have hJ : LipschitzOnWith 1 (lowPrimitive lam d) (Icc ell pHi) :=
    (hd.lowPrimitive_lipschitz.mono (Icc_subset_Icc le_rfl (by norm_num [pHi,tEnd]))).weaken (div_le_self (by norm_num) (by norm_num))
  have hglue := lipschitzOnWith_glue_Icc (a := pLo) (b := pHi) (c := ell) (by norm_num [pLo,ell]) (by norm_num [ell,pHi])
    hd.cap_mass_lipschitz hJ (lowPrimitive_at_ell lam d).symm
  have heq : EqOn (fun r => if r ≤ ell then cap lam d.S r else lowPrimitive lam d r)
      (primitive lam d) (Icc pLo pHi) := by
    intro r hr
    unfold primitive
    by_cases he : r ≤ ell
    · simp [he]
    · simp [he,hr.2.trans (by norm_num [pHi,tEnd] : pHi ≤ tEnd)]
  intro x hx y hy
  rw [← heq hx,← heq hy]
  exact hglue hx hy

theorem quadratic_unit_lipschitz {lam : ℝ} (hlam : lam ∈ Icc (0:ℝ) 1) :
    LipschitzOnWith 1 (quadratic lam) (Icc (0:ℝ) 1) := by
  apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun r _ => (quadratic_hasDerivAt lam r).hasDerivWithinAt)
  intro r hr
  change |lam-r| ≤ 1
  rw [abs_le]
  constructor <;> linarith [hlam.1,hlam.2,hr.1,hr.2]

end OptimalG.Variational
