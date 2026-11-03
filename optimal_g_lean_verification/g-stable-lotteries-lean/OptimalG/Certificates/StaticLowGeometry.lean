import OptimalG.Certificates.StaticLowAdmissible
import OptimalG.Certificates.StaticLowShape
import OptimalG.VariationalCompletedCap
import OptimalG.VariationalFiniteSlopeGlue
import OptimalG.BinaryCurveGeometry

/-! The fixed explicit low profile supplies the binary geometry for any
normalized completion with the stated head, low primitive, and straight part.
These hypotheses are identities of the actual curve, not variational feasibility. -/
namespace OptimalG.Certificates.StaticLow
open Set MeasureTheory

noncomputable def affineHeadSlope : ℝ :=
  headSlope 0.2635 (cap lam slack 0.2635) (capSlope lam slack 0.2635)

theorem completed_binaryGeometry {phi : ℝ→ℝ}
    (h : VerifierCurve phi lam)
    (hhead : ∀ r∈Icc (0:ℝ) 0.2635,phi r=phi 0+affineHeadSlope*r)
    (hlow : ∀ r∈Icc (0.2635:ℝ) 0.38,phi r=score r)
    (hprim : ∀ r∈Icc (0.2635:ℝ) 0.38,curvePrimitive phi r=primitive r)
    (hline : ∀ r∈Icc (0.38:ℝ) 0.775,phi r=(lam:ℝ)-r) :
    BinaryCurveGeometry phi lam slack affineHeadSlope leftContact := by
  have hd := Variational.staticLow_admissible
  have hcx : (leftContact:ℝ)≤(0.38:ℝ) := by linarith only [contacts_real.2.1]
  have hac : (0.2635:ℝ)≤leftContact := by linarith only [contacts_real.1]
  have hxl : (0.38:ℝ)≤lam := by norm_num [lam]
  have hlz : (lam:ℝ)≤(0.775:ℝ) := by norm_num [lam]
  have hheadLo : -(0.691:ℝ)≤affineHeadSlope := by
    convert! head_scalar_bounds.1.le using 1 <;> norm_num [affineHeadSlope]
  have hcapScore : ∀ r∈Icc (0.2635:ℝ) leftContact,
      phi r=Variational.capScore lam slack r := by
    intro r hr
    rw [hlow r ⟨hr.1,hr.2.trans hcx⟩,score_cap hr.2]
    rfl
  have hcapPrim : ∀ r∈Icc (0.2635:ℝ) leftContact,
      curvePrimitive phi r=Variational.cap lam slack r := by
    intro r hr
    rw [hprim r ⟨hr.1,hr.2.trans hcx⟩,primitive_cap hr.2]
    rfl
  have hstraight : ∀ r∈Icc (0.35945:ℝ) 0.775,phi r=(lam:ℝ)-r := by
    intro r hr
    by_cases hrx : r≤(0.38:ℝ)
    · rw [hlow r ⟨by linarith only [hr.1],hrx⟩]
      exact score_line (by linarith only [contacts_real.2.2.2,hr.1])
    · exact hline r ⟨le_of_not_ge hrx,hr.2⟩
  have hx : curvePrimitive phi (0.38:ℝ)=Variational.quadratic lam 0.38-slack := by
    rw [hprim 0.38 ⟨by norm_num,le_rfl⟩,
      primitive_line (by linarith only [contacts_real.2.2.2] : (rightContact:ℝ)≤(0.38:ℝ))]
    rfl
  have hlinePrim : ∀ r∈Icc (0.35945:ℝ) 0.775,
      curvePrimitive phi r=Variational.quadratic lam r-slack := by
    have ht : curvePrimitive phi (0.35945:ℝ)=Variational.quadratic lam 0.35945-slack := by
      rw [hprim 0.35945 ⟨by norm_num,by norm_num⟩,
        primitive_line contacts_real.2.2.2.le]
      rfl
    exact h.primitive_eq_quadratic_on_line (by norm_num) (by norm_num) (by norm_num)
      ht hstraight
  have hcapUpper : ∀ r∈Icc (0:ℝ) 0.53,
      curvePrimitive phi r≤Variational.cap lam slack r := by
    have hheadCap := Variational.head_primitive_le_cap hd h
      hhead (hcapScore 0.2635 ⟨le_rfl,hac⟩) (hcapPrim 0.2635 ⟨le_rfl,hac⟩)
    intro r hr
    by_cases hra : r≤(0.2635:ℝ)
    · exact hheadCap r ⟨hr.1,hra⟩
    · by_cases hrx : r≤(0.38:ℝ)
      · rw [hprim r ⟨le_of_not_ge hra,hrx⟩]
        exact primitive_le_cap (by linarith only [hrx])
      · have hquad := h.primitive_le_quadratic_after_anchor
          (by constructor <;> norm_num : (0.38:ℝ)∈Icc (0:ℝ) 1) hx r
          ⟨le_of_not_ge hrx,by linarith only [hr.2]⟩
        apply hquad.trans
        exact hd.cap_ge_quadratic_after_xHi r
          (by have hh := le_of_not_ge hrx; norm_num [Variational.xHi] at hh ⊢; exact ⟨hh,by convert! hr.2 using 1 <;> norm_num⟩)
  have hpre : ∀ r∈Icc (0:ℝ) leftContact,∀ s∈Icc (0:ℝ) leftContact,r≤s →
      affineHeadSlope*(s-r)≤phi s-phi r := by
    apply Variational.lower_increment_glue (by norm_num : (0:ℝ)≤0.2635) hac
    · intro r hr s hs hrs
      rw [hhead r hr,hhead s hs]
      ring_nf
      exact le_rfl
    · intro r hr s hs hrs
      rw [hlow r ⟨hr.1,hr.2.trans hcx⟩,hlow s ⟨hs.1,hs.2.trans hcx⟩]
      exact cap_pre_increment hr.1 hrs hs.2
  have hpost : ∀ r∈Icc (leftContact:ℝ) 1,∀ s∈Icc (leftContact:ℝ) 1,r≤s →
      phi s-phi r≤-(0.691:ℝ)*(s-r) := by
    apply Variational.upper_increment_glue (hcx.trans hxl) h.lam_lt_one.le
    · apply Variational.upper_increment_glue hcx hxl
      · intro r hr s hs hrs
        rw [hlow r ⟨hac.trans hr.1,hr.2⟩,hlow s ⟨hac.trans hs.1,hs.2⟩]
        convert! (score_post_increment hr.1 hrs).2 using 1 <;> norm_num
      · intro r hr s hs hrs
        rw [hline r ⟨hr.1,hr.2.trans hlz⟩,hline s ⟨hs.1,hs.2.trans hlz⟩]
        linarith only [hrs]
    · intro r hr s hs hrs
      have hh := h.high_fall r s hr.1 hrs hs.2
      linarith only [hh,hrs]
  have hlowSlope : ∀ r∈Icc (0:ℝ) lam,∀ s∈Icc (0:ℝ) lam,r≤s →
      -1*(s-r)≤phi s-phi r := by
    apply Variational.lower_increment_glue (by norm_num : (0:ℝ)≤0.2635)
      ((by norm_num : (0.2635:ℝ)≤0.38).trans hxl)
    · intro r hr s hs hrs
      rw [hhead r hr,hhead s hs]
      have hm := mul_le_mul_of_nonneg_right (show -1≤affineHeadSlope by linarith only [hheadLo])
        (sub_nonneg.mpr hrs)
      nlinarith only [hm]
    · apply Variational.lower_increment_glue (by norm_num : (0.2635:ℝ)≤0.38) hxl
      · intro r hr s hs hrs
        rw [hlow r hr,hlow s hs]
        have hh := score_lower_increment r ⟨hr.1,by linarith only [hr.2]⟩
          s ⟨hs.1,by linarith only [hs.2]⟩ hrs
        linarith only [hh]
      · intro r hr s hs hrs
        rw [hline r ⟨hr.1,hr.2.trans hlz⟩,hline s ⟨hs.1,hs.2.trans hlz⟩]
        ring_nf
        exact le_rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hpre,?_,?_,?_,?_⟩
  · norm_num [lam]
  · have hh := contacts_real
    norm_num at hh ⊢
    exact ⟨hh.1.le,hh.2.1.le⟩
  · convert! hhead using 1 <;> norm_num
  · convert! hcapPrim using 1 <;> norm_num
  · convert! hcapScore using 1 <;> norm_num
  · convert! hcapUpper using 1 <;> norm_num
  · convert! hstraight using 1 <;> norm_num
  · convert! hlinePrim using 1 <;> norm_num
  · convert! hpost using 1 <;> norm_num
  · convert! hheadLo using 1 <;> norm_num
  · intro r hr s hs hrs
    have hr' : r∈Icc (0.2635:ℝ) leftContact := by convert! hr using 1 <;> norm_num
    have hs' : s∈Icc (0.2635:ℝ) leftContact := by convert! hs using 1 <;> norm_num
    rw [hlow r ⟨hr'.1,hr'.2.trans hcx⟩,hlow s ⟨hs'.1,hs'.2.trans hcx⟩]
    have hh := cap_lower_increment hrs (hs'.2.trans (by linarith only [contacts_real.2.1]))
    rw [score_cap hs'.2,score_cap hr'.2]
    linarith only [hh,hrs]
  · intro r s hr hrs hs
    have hh := hlowSlope r ⟨hr,hrs.trans hs⟩ s ⟨hr.trans hrs,hs⟩ hrs
    linarith only [hh]

end OptimalG.Certificates.StaticLow
