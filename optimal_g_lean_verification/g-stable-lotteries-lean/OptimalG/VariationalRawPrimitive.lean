import OptimalG.VariationalMassLipschitz
import OptimalG.SignedRationalControl

/-! A bounded Lipschitz extension of the actual variational primitive. Its
raw control agrees with the original control throughout the continuation. -/
namespace OptimalG.Variational
open Set MeasureTheory
open scoped NNReal

theorem Admissible.primitive_interval_lipschitz {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : LipschitzOnWith 1 (primitive lam d) (Icc pLo zStart) := by
  have hL : lam ∈ Icc (0 : ℝ) 1 := by
    have hh := hd.compact_lambdaRange
    constructor <;> linarith [hh.1,hh.2]
  have hq0 := (quadratic_unit_lipschitz hL).mono
    (Icc_subset_Icc (by norm_num [tEnd] : (0 : ℝ) ≤ tEnd)
      (by norm_num [zStart] : zStart ≤ 1))
  have hq : LipschitzOnWith 1 (fun r => quadratic lam r-d.S) (Icc tEnd zStart) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simpa only [dist_sub_right] using hq0.dist_le_mul a ha b hb
  have hl : LipschitzOnWith 1 (lowPrimitive lam d) (Icc ell tEnd) :=
    hd.lowPrimitive_lipschitz.weaken (div_le_self (by norm_num) (by norm_num))
  have hinner := lipschitzOnWith_glue_Icc (a := ell) (b := zStart) (c := tEnd)
    (by norm_num [ell,tEnd]) (by norm_num [tEnd,zStart]) hl hq hd.2.2.2.2.1
  have he : cap lam d.S ell =
      (if ell ≤ tEnd then lowPrimitive lam d ell else quadratic lam ell-d.S) := by
    rw [if_pos (by norm_num [ell,tEnd] : ell ≤ tEnd),lowPrimitive_at_ell]
  exact lipschitzOnWith_glue_Icc (by norm_num [pLo,ell]) (by norm_num [ell,zStart])
    hd.cap_mass_lipschitz hinner he

noncomputable def clippedPrimitive (lam : ℝ) (d : LowRankData) (r : ℝ) : ℝ :=
  primitive lam d (projIcc pLo zStart (by norm_num [pLo,zStart]) r)

theorem clippedPrimitive_eq (lam : ℝ) (d : LowRankData) {r : ℝ}
    (hr : r ∈ Icc pLo zStart) : clippedPrimitive lam d r=primitive lam d r := by
  simp only [clippedPrimitive,projIcc_of_mem (by norm_num [pLo,zStart] : pLo ≤ zStart) hr]

theorem Admissible.clippedPrimitive_lipschitz {lam : ℝ} {d : LowRankData}
    (hd : Admissible lam d) : LipschitzWith 1 (clippedPrimitive lam d) := by
  unfold clippedPrimitive
  convert! hd.primitive_interval_lipschitz.to_restrict.comp
    (LipschitzWith.projIcc (by norm_num [pLo,zStart] : pLo ≤ zStart)) using 1 <;> simp

theorem primitive_plateau (lam : ℝ) (d : LowRankData) {r : ℝ} (hr : tEnd < r) :
    primitive lam d r=quadratic lam r-d.S := by
  have he : ¬r ≤ ell := by
    have hh : ell ≤ tEnd := by norm_num [ell,tEnd]
    linarith
  simp only [primitive,if_neg he,if_neg (not_le.mpr hr)]

theorem clippedPrimitive_control_values (lam : ℝ) (d : LowRankData)
    {c : Control} (hc : c ∈ controlDomain) {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    clippedPrimitive lam d c.1=primitive lam d c.1 ∧
      clippedPrimitive lam d (1-c.1)=quadratic lam (1-c.1)-d.S ∧
      clippedPrimitive lam d (z-c.1)=quadratic lam (z-c.1)-d.S := by
  have hp : c.1 ∈ Icc (0.25 : ℝ) 0.36 := by
    convert! hc.1 using 1 <;> norm_num [pLo,pHi]
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by
    convert! hz using 1 <;> norm_num [zStart,zEnd]
  refine ⟨clippedPrimitive_eq lam d ⟨hc.1.1,hc.1.2.trans (by norm_num [pHi,zStart])⟩,?_,?_⟩
  · rw [clippedPrimitive_eq lam d (by
      constructor <;> norm_num [pLo,zStart] <;> linarith [hp.1,hp.2])]
    exact primitive_plateau lam d (by norm_num [tEnd]; linarith [hp.2])
  · rw [clippedPrimitive_eq lam d (by
      constructor <;> norm_num [pLo,zStart] <;> linarith [hp.1,hp.2,hz'.1,hz'.2])]
    exact primitive_plateau lam d (by norm_num [tEnd]; linarith [hp.2,hz'.1])

theorem rawControl_clippedPrimitive (lam : ℝ) (d : LowRankData) (u : ℝ)
    {c : Control} (hc : c ∈ controlDomain) {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    signedControlH lam (clippedPrimitive lam d) (rawAlpha lam (clippedPrimitive lam d) d.phi)
      (rawBeta lam (clippedPrimitive lam d) d.phi) (·.1) z u c=controlH lam d z u c := by
  obtain ⟨hR,hP,hK⟩ := clippedPrimitive_control_values lam d hc hz
  rw [rawControl_eq_value,hR,hP,hK,controlH_eq_certified_value]

theorem rawVectorField_clippedPrimitive (lam : ℝ) (d : LowRankData) (u : ℝ)
    {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    rawVectorField lam (clippedPrimitive lam d) d.phi z u=vectorField lam d z u := by
  unfold rawVectorField signedVectorField vectorField
  congr 1
  apply essInf_congr_ae
  filter_upwards [ae_restrict_mem controlDomain_measurable] with c hc
  exact rawControl_clippedPrimitive lam d u hc hz

end OptimalG.Variational
