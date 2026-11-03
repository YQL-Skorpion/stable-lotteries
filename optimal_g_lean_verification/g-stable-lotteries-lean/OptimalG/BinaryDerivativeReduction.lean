import OptimalG.BinaryEndpoint

/-! The central-mass extension from a checked small split strip. This uses
finite score increment bounds and needs no derivative of the score itself. -/
namespace OptimalG
open Set

noncomputable def normalizedBinaryTest (phi : ℝ → ℝ) (p q : ℝ) : ℝ :=
  q+(p/curvePrimitive phi p)*packingDelta phi p q

namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

theorem normalizedBinaryTest_hasDerivAt {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : 0 < q) (hqp : q < p) :
    HasDerivAt (normalizedBinaryTest phi p)
      (1+(p/curvePrimitive phi p)*(phi (q+1-p)-phi q)) q := by
  have hi := ((hasDerivAt_const q (1-p)).add (hasDerivAt_id q))
  have hshift : 1-p+q ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith⟩
  have hnum := ((h.primitive_hasDerivAt hshift).comp q hi).sub
    (h.primitive_hasDerivAt ⟨hq,hqp.trans hp.2⟩)
  have hd := (hasDerivAt_id q).add (hnum.const_mul (p/curvePrimitive phi p))
  convert! hd using 1 <;> first | rfl |
    (simp only [id_eq,zero_add,mul_one]; congr 2 <;> ring)

theorem normalizedBinaryTest_continuousOn {p a b : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (ha : 0 ≤ a) (hbp : b ≤ p) :
    ContinuousOn (normalizedBinaryTest phi p) (Icc a b) := by
  have hn := (h.binary_numerator_continuousOn hp).mono (Icc_subset_Icc ha hbp)
  have he : normalizedBinaryTest phi p=(fun q => q+(p/curvePrimitive phi p)*
      (curvePrimitive phi (q+1-p)-curvePrimitive phi q)) := by
    ext q
    unfold normalizedBinaryTest packingDelta
    congr 3 <;> ring
  rw [he]
  exact continuous_id.continuousOn.add (hn.const_mul _)

/-- A single derivative numerator at a controls every larger split in a band. -/
theorem normalizedBinaryTest_antitone_band {p a b : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) (hab : a ≤ b) (hbp : b ≤ p)
    (hlow : ∀ q ∈ Icc a b,a-q ≤ phi q-phi a)
    (hhigh : ∀ q ∈ Icc a b,phi (q+1-p)-phi (a+1-p) ≤ a-q)
    (hanchor : curvePrimitive phi p+p*(phi (a+1-p)-phi a) ≤ 0) :
    AntitoneOn (normalizedBinaryTest phi p) (Icc a b) := by
  have hd (q : ℝ) (hq : q ∈ interior (Icc a b)) :
      HasDerivAt (normalizedBinaryTest phi p)
        (1+(p/curvePrimitive phi p)*(phi (q+1-p)-phi q)) q := by
    rw [interior_Icc] at hq
    exact h.normalizedBinaryTest_hasDerivAt hp (ha.trans_lt hq.1) (hq.2.trans_le hbp)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (h.normalizedBinaryTest_continuousOn hp ha hbp)
    (fun q hq => (hd q hq).differentiableAt.differentiableWithinAt)
  intro q hq
  rw [(hd q hq).deriv]
  have hq' := interior_subset hq
  have hscore : phi (q+1-p)-phi q ≤ phi (a+1-p)-phi a := by
    linarith [hlow q hq',hhigh q hq']
  have hm := mul_le_mul_of_nonneg_left hscore hp.1.le
  have hnum : p*(phi (q+1-p)-phi q) ≤ -curvePrimitive phi p := by linarith
  have hquot := div_le_div_of_nonneg_right hnum (h.primitive_pos hp).le
  rw [← div_mul_eq_mul_div] at hquot
  have hz : (-curvePrimitive phi p)/curvePrimitive phi p= -1 := by
    simp [ne_of_gt (h.primitive_pos hp)]
  rw [hz] at hquot
  linarith

/-- A finite head-strip certificate plus one slope check covers the whole band. -/
theorem binary_of_initial_strip {p a b : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) (hab : a ≤ b) (hbp : b ≤ p)
    (hlow : ∀ q ∈ Icc a b,a-q ≤ phi q-phi a)
    (hhigh : ∀ q ∈ Icc a b,phi (q+1-p)-phi (a+1-p) ≤ a-q)
    (hanchor : curvePrimitive phi p+p*(phi (a+1-p)-phi a) ≤ 0)
    (hhead : ∀ q ∈ Icc (0 : ℝ) a,normalizedBinaryTest phi p q ≤ lam) :
    ∀ q ∈ Icc (0 : ℝ) b,normalizedBinaryTest phi p q ≤ lam := by
  have hm := h.normalizedBinaryTest_antitone_band hp ha hab hbp hlow hhigh hanchor
  intro q hq
  by_cases hqa : q ≤ a
  · exact hhead q ⟨hq.1,hqa⟩
  · exact (hm ⟨le_rfl,hab⟩ ⟨(lt_of_not_ge hqa).le,hq.2⟩ (lt_of_not_ge hqa).le).trans
      (hhead a ⟨ha,le_rfl⟩)

end VerifierCurve
end OptimalG
