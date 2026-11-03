import OptimalG.VariationalAverages

/-!
# Dependence of rational control coefficients on admissible data

The score values occur linearly in H. All remaining coefficients converge
pointwise under scalar-parameter and primitive convergence; their denominators
stay uniformly positive by the already proved admissibility bounds.
-/

namespace OptimalG.Variational

open Set MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

noncomputable def controlCoeffX (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) : ℝ :=
  -((z - lam) * primitive lam d c.1 +
    (quadratic lam (z - c.1) - d.S - u) * (c.1 + c.2.2 - lam)) /
      controlDeterminant lam d c

noncomputable def controlCoeffY (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) : ℝ :=
  -((z - lam) * (quadratic lam (1 - c.1) - d.S) +
    (quadratic lam (z - c.1) - d.S - u) * (2 * lam - c.2.1)) /
      controlDeterminant lam d c

theorem controlH_linear_scores (lam : ℝ) (d : LowRankData) (z u : ℝ) (c : Control) :
    controlH lam d z u c = controlCoeffX lam d z u c * d.phi c.2.1 +
      controlCoeffY lam d z u c * d.phi c.2.2 := by
  unfold controlH controlCoeffX controlCoeffY
  ring

theorem primitive_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (r : ℝ) : Tendsto (fun n => primitive (lamn n) (dn n) r) atTop (𝓝 (primitive lam d r)) := by
  unfold primitive
  split_ifs with he ht
  · exact (((hlam.pow 2).sub (hlam.div_const 2)).add ((hlam.mul_const r).div_const 2)).sub
      ((hlam.mul hS).div_const (1 - r))
  · exact hJ.tendsto_at ⟨r, ⟨le_of_lt (lt_of_not_ge he), ht⟩⟩
  · exact ((hlam.mul_const r).sub tendsto_const_nhds).sub hS

theorem controlDeterminant_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (c : Control) :
    Tendsto (fun n => controlDeterminant (lamn n) (dn n) c) atTop (𝓝 (controlDeterminant lam d c)) := by
  have hR := primitive_tendsto_of_data lamn dn hn hd hlam hS hJ c.1
  have hP : Tendsto (fun n => quadratic (lamn n) (1 - c.1) - (dn n).S)
      atTop (𝓝 (quadratic lam (1 - c.1) - d.S)) :=
    ((hlam.mul_const (1 - c.1)).sub tendsto_const_nhds).sub hS
  exact (((hlam.const_mul 2).sub_const c.2.1).mul hR).sub
    ((tendsto_const_nhds.sub hlam).mul hP)

theorem control_coefficients_tendsto_of_data
    (lamn : ℕ → ℝ) (dn : ℕ → LowRankData) (hn : ∀ n, Admissible (lamn n) (dn n))
    {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (hlam : Tendsto lamn atTop (𝓝 lam))
    (hS : Tendsto (fun n => (dn n).S) atTop (𝓝 d.S))
    (hJ : TendstoUniformly (fun n => lowPrimitiveMap (hn n)) (lowPrimitiveMap hd) atTop)
    (z u : ℝ) {c : Control} (hc : c ∈ controlDomain) :
    Tendsto (fun n => controlCoeffX (lamn n) (dn n) z u c) atTop (𝓝 (controlCoeffX lam d z u c)) ∧
    Tendsto (fun n => controlCoeffY (lamn n) (dn n) z u c) atTop (𝓝 (controlCoeffY lam d z u c)) := by
  have hR := primitive_tendsto_of_data lamn dn hn hd hlam hS hJ c.1
  have hP : Tendsto (fun n => quadratic (lamn n) (1 - c.1) - (dn n).S)
      atTop (𝓝 (quadratic lam (1 - c.1) - d.S)) :=
    ((hlam.mul_const (1 - c.1)).sub tendsto_const_nhds).sub hS
  have hQ : Tendsto (fun n => quadratic (lamn n) (z - c.1) - (dn n).S - u)
      atTop (𝓝 (quadratic lam (z - c.1) - d.S - u)) :=
    (((hlam.mul_const (z - c.1)).sub tendsto_const_nhds).sub hS).sub_const u
  have hD := controlDeterminant_tendsto_of_data lamn dn hn hd hlam hS hJ c
  have hDne : controlDeterminant lam d c ≠ 0 := by linarith [hd.determinant_positive hc]
  constructor
  · exact (((tendsto_const_nhds.sub hlam).mul hR).add
      (hQ.mul (tendsto_const_nhds.sub hlam))).neg.div hD hDne
  · exact (((tendsto_const_nhds.sub hlam).mul hP).add
      (hQ.mul ((hlam.const_mul 2).sub_const c.2.1))).neg.div hD hDne

noncomputable def controlCoeffBound (z u : ℝ) : ℝ :=
  100 * (2 * (|z| + 1) + 3 * ((|z| + 1) + (|z| + 1) ^ 2 / 2 + 1 + |u|))

/-- A uniform bound independent of the admissible pair. Its purpose is dominated
convergence; sharp numerical estimates are unnecessary here. -/
theorem Admissible.control_coefficients_bound {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (z u : ℝ) {c : Control} (hc : c ∈ controlDomain) :
    |controlCoeffX lam d z u c| ≤ controlCoeffBound z u ∧
      |controlCoeffY lam d z u c| ≤ controlCoeffBound z u := by
  have hlo := h.1.1
  have hhi := h.1.2
  have hSlo := h.slack_lower
  have hShi := h.slack_upper
  have hp := hc.1
  have hx := hc.2.1
  have hylo := (le_max_left xLo c.1).trans hc.2.2.1
  have hyhi := hc.2.2.2
  norm_num [lambdaLo, lambdaHi, pLo, pHi, xLo, xHi] at hlo hhi hp hx hylo hyhi
  have hlam : |lam| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hS : |d.S| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hpa : |c.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hk : |c.1 + c.2.2 - lam| ≤ 3 := abs_le.mpr
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have hh : |2 * lam - c.2.1| ≤ 3 := abs_le.mpr
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hR : |primitive lam d c.1| ≤ 2 := by
    rw [abs_of_nonneg (show 0 ≤ primitive lam d c.1 by linarith [h.control_R_lower hc.1])]
    exact h.control_R_upper hc.1
  have hP : |quadratic lam (1 - c.1) - d.S| ≤ 2 := by
    rw [abs_of_nonneg (h.control_P_bounds hc.1).1]
    linarith [(h.control_P_bounds hc.1).2]
  let Z := |z| + 1
  let B := Z + Z ^ 2 / 2 + 1 + |u|
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzl : |z - lam| ≤ Z := (abs_sub z lam).trans (add_le_add le_rfl hlam)
  have hzp : |z - c.1| ≤ Z := (abs_sub z c.1).trans (add_le_add le_rfl hpa)
  have hzp2 : |z - c.1| ^ 2 ≤ Z ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzp) (add_nonneg hZ (abs_nonneg (z - c.1)))]
  have hQ0 : |quadratic lam (z - c.1)| ≤ Z + Z ^ 2 / 2 := by
    calc
      _ ≤ |lam * (z - c.1)| + |(z - c.1) ^ 2 / 2| := abs_sub _ _
      _ = |lam| * |z - c.1| + |z - c.1| ^ 2 / 2 := by
        norm_num [abs_mul, abs_div, abs_pow]
      _ ≤ 1 * Z + Z ^ 2 / 2 := add_le_add
        (mul_le_mul hlam hzp (abs_nonneg _) zero_le_one) (by linarith)
      _ = _ := by ring
  have hQ : |quadratic lam (z - c.1) - d.S - u| ≤ B := by
    have h1 := abs_sub (quadratic lam (z - c.1) - d.S) u
    have h2 := abs_sub (quadratic lam (z - c.1)) d.S
    dsimp [B]
    linarith
  have hnum (R : ℝ) (hRa : |R| ≤ 2) (k : ℝ) (hka : |k| ≤ 3) :
      |(z - lam) * R + (quadratic lam (z - c.1) - d.S - u) * k| ≤ 2 * Z + 3 * B := by
    calc
      _ ≤ |(z - lam) * R| + |(quadratic lam (z - c.1) - d.S - u) * k| := abs_add_le _ _
      _ = |z - lam| * |R| + |quadratic lam (z - c.1) - d.S - u| * |k| := by simp only [abs_mul]
      _ ≤ Z * 2 + B * 3 := add_le_add
        (mul_le_mul hzl hRa (abs_nonneg _) hZ) (mul_le_mul hQ hka (abs_nonneg _) hB)
      _ = _ := by ring
  have hdet := h.determinant_positive hc
  have hdpos : 0 < controlDeterminant lam d c := by linarith
  have hdivide (v : ℝ) (hv : |v| ≤ 2 * Z + 3 * B) :
      |-v / controlDeterminant lam d c| ≤ 100 * (2 * Z + 3 * B) := by
    rw [abs_div, abs_neg, abs_of_pos hdpos]
    apply (div_le_iff₀ hdpos).mpr
    have hb : 0 ≤ 2 * Z + 3 * B := by positivity
    have hp := mul_nonneg hb (show 0 ≤ 100 * controlDeterminant lam d c - 1 by linarith)
    nlinarith
  exact ⟨hdivide _ (hnum _ hR _ hk), hdivide _ (hnum _ hP _ hh)⟩

end OptimalG.Variational
