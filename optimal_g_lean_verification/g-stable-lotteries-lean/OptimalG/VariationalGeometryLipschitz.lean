import OptimalG.VariationalFeatureBounds
import OptimalG.VariationalMassLipschitz
import OptimalG.VariationalControlArguments

/-! A uniform finite Lipschitz bound for the geometric mass/rank change in B.6. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped Topology NNReal

noncomputable def geometricArguments {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    (w : (ℝ × ℝ) × ControlFeature) : Certificates.Control.Arguments :=
  ![w.1.1-lam, 2*lam-w.2.1.2.1, w.2.1.1+w.2.1.2.2-lam,
    controlPrimitiveExtension hd w.2.1.1, quadratic lam (1-w.2.1.1)-d.S,
    quadratic lam (w.1.1-w.2.1.1)-d.S-w.1.2,w.2.2.1,w.2.2.2]

noncomputable def geometricDomain : Set ((ℝ × ℝ) × ControlFeature) :=
  (Icc zStart zEnd ×ˢ Icc (-10:ℝ) 10) ×ˢ
    (controlDomain ×ˢ (Icc (0:ℝ) (278/1000) ×ˢ Icc (0:ℝ) (278/1000)))

theorem geometricDomain_compact : IsCompact geometricDomain :=
  (isCompact_Icc.prod isCompact_Icc).prod (controlDomain_isCompact.prod (isCompact_Icc.prod isCompact_Icc))

theorem geometricArguments_continuous {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    Continuous (geometricArguments hd) := by
  have hR := controlPrimitiveExtension_continuous hd
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [geometricArguments,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons] <;>
    unfold quadratic <;> fun_prop

theorem geometricArguments_det {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {w : (ℝ × ℝ) × ControlFeature} (hw : w ∈ geometricDomain) :
    Certificates.Control.argumentsDet (geometricArguments hd w) = controlDeterminant lam d w.2.1 := by
  simp only [Certificates.Control.argumentsDet,geometricArguments,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  rw [controlPrimitiveExtension_eq hd hw.2.1.1]
  rfl

theorem geometricArguments_value {lam : ℝ} {d : LowRankData} (hd : Admissible lam d)
    {w : (ℝ × ℝ) × ControlFeature} (hw : w.2.1 ∈ controlDomain) :
    Certificates.Control.argumentsValue (geometricArguments hd w) = featureH hd w.1.1 w.1.2 w.2 := by
  rw [featureH_eq_value hd w.1.1 w.1.2 w.2.2.1 w.2.2.2 hw]
  simp only [Certificates.Control.argumentsValue,geometricArguments,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  rw [controlPrimitiveExtension_eq hd hw.1]
  rfl

theorem Admissible.geometricArguments_value_lipschitz {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    ∃ L : ℝ≥0, LipschitzOnWith L Certificates.Control.argumentsValue (geometricArguments hd '' geometricDomain) := by
  apply Certificates.Control.argumentsValue_lipschitz_compact
    (geometricDomain_compact.image (geometricArguments_continuous hd))
  rintro v ⟨w,hw,rfl⟩
  rw [geometricArguments_det hd hw]
  linarith [hd.determinant_positive hw.2.1]

theorem Admissible.geometricArguments_dist {lam z u p q x y t A B : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hz : z ∈ Icc zStart zEnd)
    (hp : p ∈ Icc pLo pHi) (hq : q ∈ Icc pLo pHi) :
    dist (geometricArguments hd ((z,u),((p,x,y),A,B)))
      (geometricArguments hd ((z,u),((q,x,t),A,B))) ≤ |p-q|+|y-t| := by
  have hl : lam ∈ Icc (0:ℝ) 1 := by
    have hh := hd.1
    norm_num [lambdaLo,lambdaHi] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hQ := quadratic_unit_lipschitz hl
  have hp1 : 1-p ∈ Icc (0:ℝ) 1 := by
    have hh := hp
    norm_num [pLo,pHi] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hq1 : 1-q ∈ Icc (0:ℝ) 1 := by
    have hh := hq
    norm_num [pLo,pHi] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hzp : z-p ∈ Icc (0:ℝ) 1 := by
    have hp' := hp
    have hz' := hz
    norm_num [pLo,pHi,zStart,zEnd] at hp' hz'
    constructor <;> linarith [hp'.1,hp'.2,hz'.1,hz'.2]
  have hzq : z-q ∈ Icc (0:ℝ) 1 := by
    have hq' := hq
    have hz' := hz
    norm_num [pLo,pHi,zStart,zEnd] at hq' hz'
    constructor <;> linarith [hq'.1,hq'.2,hz'.1,hz'.2]
  have hR : dist (controlPrimitiveExtension hd p) (controlPrimitiveExtension hd q) ≤ |p-q| := by
    rw [controlPrimitiveExtension_eq hd hp,controlPrimitiveExtension_eq hd hq]
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hd.primitive_mass_lipschitz.dist_le_mul p hp q hq
  have hP : dist (quadratic lam (1-p)-d.S) (quadratic lam (1-q)-d.S) ≤ |p-q| := by
    simpa only [dist_sub_right,dist_sub_left,NNReal.coe_one,one_mul,Real.dist_eq] using hQ.dist_le_mul (1-p) hp1 (1-q) hq1
  have hK : dist (quadratic lam (z-p)-d.S-u) (quadratic lam (z-q)-d.S-u) ≤ |p-q| := by
    simpa only [dist_sub_right,dist_sub_left,NNReal.coe_one,one_mul,Real.dist_eq] using hQ.dist_le_mul (z-p) hzp (z-q) hzq
  have hk : dist (p+y-lam) (q+t-lam) ≤ |p-q|+|y-t| := by
    simpa only [dist_sub_right,Real.dist_eq] using dist_add_add_le p y q t
  have htotal : 0 ≤ |p-q|+|y-t| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  apply (dist_pi_le_iff htotal).mpr
  intro i
  fin_cases i <;> simp only [geometricArguments,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,dist_self]
  · change dist (z-lam) (z-lam) ≤ |p-q|+|y-t|
    simpa only [dist_self] using htotal
  · change dist (2*lam-x) (2*lam-x) ≤ |p-q|+|y-t|
    simpa only [dist_self] using htotal
  · exact hk
  · exact hR.trans (le_add_of_nonneg_right (abs_nonneg _))
  · exact hP.trans (le_add_of_nonneg_right (abs_nonneg _))
  · exact hK.trans (le_add_of_nonneg_right (abs_nonneg _))
  · change dist (A) (A) ≤ |p-q|+|y-t|
    simpa only [dist_self] using htotal
  · change dist (B) (B) ≤ |p-q|+|y-t|
    simpa only [dist_self] using htotal

/-- The coupled geometric shift has a uniform Lipschitz bound for all times,
states and score values in the compact domain. -/
theorem Admissible.geometric_control_lipschitz {lam : ℝ} {d : LowRankData} (hd : Admissible lam d) :
    ∃ L : ℝ≥0, ∀ z ∈ Icc zStart zEnd, ∀ u ∈ Icc (-10:ℝ) 10,
      ∀ p q x y t A B : ℝ, (p,x,y) ∈ controlDomain → (q,x,t) ∈ controlDomain →
      A ∈ Icc (0:ℝ) (278/1000) → B ∈ Icc (0:ℝ) (278/1000) →
      |featureH hd z u ((p,x,y),A,B)-featureH hd z u ((q,x,t),A,B)| ≤ L*(|p-q|+|y-t|) := by
  obtain ⟨L,hL⟩ := hd.geometricArguments_value_lipschitz
  refine ⟨L,?_⟩
  intro z hz u hu p q x y t A B hc hc' hA hB
  have hw : ((z,u),((p,x,y),A,B)) ∈ geometricDomain := ⟨⟨hz,hu⟩,hc,hA,hB⟩
  have hw' : ((z,u),((q,x,t),A,B)) ∈ geometricDomain := ⟨⟨hz,hu⟩,hc',hA,hB⟩
  have hh := hL.dist_le_mul _ (mem_image_of_mem _ hw) _ (mem_image_of_mem _ hw')
  rw [geometricArguments_value hd hc,geometricArguments_value hd hc',Real.dist_eq] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hd.geometricArguments_dist hz hc.1 hc'.1) L.coe_nonneg)

end OptimalG.Variational
