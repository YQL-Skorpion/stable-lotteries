import OptimalG.Certificates.ReferenceFlowExpressions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! A checked finite time partition defines a measurable reference field.
The finite bounds imply genuine interval integrability, including all joins. -/
namespace OptimalG.Certificates
open Set MeasureTheory
namespace RatExpr

theorem measurable_eval {n : ℕ} {x : ℝ→Fin n→ℝ}
    (hx : ∀ i,Measurable (fun t => x t i)) (e : RatExpr n) :
    Measurable (fun t => e.eval (x t)) := by
  induction e with
  | const q => exact measurable_const
  | var i => exact hx i
  | neg e ih => exact ih.neg
  | add e f ihe ihf => exact ihe.add ihf
  | mul e f ihe ihf => exact ihe.mul ihf
  | inv e ih => exact ih.inv

theorem measurable_evalOne (e : RatExpr 1) : Measurable e.evalOne :=
  measurable_eval (fun _ => measurable_id) e

def integerAbsCheck (scale : ℕ) (e : RatExpr 1) (bound : ℤ) : Bool :=
  match e.integerInterval scale (fun _ => IntegerInterval.fromRat scale ⟨0,1⟩) with
  | none => false
  | some out => decide (out.maxAbs≤bound)

theorem integerAbsCheck_sound {scale : ℕ} (hs : 0<scale) (e : RatExpr 1)
    (bound : ℤ) (hc : e.integerAbsCheck scale bound=true) {t : ℝ}
    (ht : t∈Icc (0:ℝ) 1) : |e.evalOne t|≤(bound:ℝ)/(scale:ℝ) := by
  cases he : e.integerInterval scale (fun _ => IntegerInterval.fromRat scale ⟨0,1⟩) with
  | none => simp [integerAbsCheck,he] at hc
  | some out =>
    have hb : out.maxAbs≤bound := by simpa [integerAbsCheck,he] using hc
    have h := integerInterval_sound hs _ (fun _ => t) (fun _ =>
      IntegerInterval.fromRat_contains hs (by simpa [RatInterval.Contains] using ht)) e he
    exact (IntegerInterval.abs_bound hs h).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hb) (Nat.cast_nonneg _))

end RatExpr
namespace Transport
namespace ReferenceFlowCell

noncomputable def timeParameter (c : ReferenceFlowCell) (z : ℝ) : ℝ :=
  (z-c.segment.left.z)/(c.length:ℝ)

theorem timeParameter_mem {c : ReferenceFlowCell}
    (hc : c.segment.left.z<c.segment.right.z) {z : ℝ}
    (hz : z∈Icc (c.segment.left.z:ℝ) c.segment.right.z) :
    c.timeParameter z∈Icc (0:ℝ) 1 := by
  have hl : (0:ℝ)<c.length := by
    exact_mod_cast (sub_pos.mpr hc : 0<c.segment.right.z-c.segment.left.z)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hz.1) hl.le
  · apply (div_le_one hl).mpr
    simp only [length,Rat.cast_sub]
    linarith [hz.2]

theorem timeParameter_measurable (c : ReferenceFlowCell) : Measurable c.timeParameter :=
  (measurable_id.sub measurable_const).div_const _

theorem actualAlpha_measurable (c : ReferenceFlowCell) : Measurable c.actualAlpha := by
  have h := RatExpr.measurable_evalOne c.alphaExpr
  convert h using 1
  funext t
  exact (c.alphaExpr_eval t).symm

theorem actualBeta_measurable (c : ReferenceFlowCell) : Measurable c.actualBeta := by
  have h := RatExpr.measurable_evalOne c.betaExpr
  convert h using 1
  funext t
  exact (c.betaExpr_eval t).symm

end ReferenceFlowCell

def referenceFlowCoverCheck (start finish : ℚ) : List ReferenceFlowCell→Bool
  | [] => decide (start=finish)
  | c::cs => decide (c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z) &&
      referenceFlowCoverCheck c.segment.right.z finish cs

noncomputable def referenceField (field : ReferenceFlowCell→ℝ→ℝ) :
    List ReferenceFlowCell→ℝ→ℝ
  | [],_ => 0
  | c::cs,z => if z≤c.segment.right.z then field c (c.timeParameter z)
      else referenceField field cs z

theorem referenceField_measurable (field : ReferenceFlowCell→ℝ→ℝ)
    (hm : ∀ c,Measurable (field c)) (cells : List ReferenceFlowCell) :
    Measurable (referenceField field cells) := by
  induction cells with
  | nil => exact measurable_const
  | cons c cs ih =>
    exact Measurable.ite (measurableSet_le measurable_id measurable_const)
      ((hm c).comp c.timeParameter_measurable) ih

/-- The selected branch agrees with one certified cell at every time except
the leftmost endpoint. No ordering assumption is external to the checker. -/
theorem referenceField_selected (field : ReferenceFlowCell→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell}
    (hc : referenceFlowCoverCheck start finish cells=true)
    {z : ℝ} (hz : z∈Ioc (start:ℝ) finish) :
    ∃ c∈cells,c.segment.left.z<c.segment.right.z ∧
      z∈Ioc (c.segment.left.z:ℝ) c.segment.right.z ∧
      referenceField field cells z=field c (c.timeParameter z) := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    rw [he] at hz
    exact False.elim (not_lt_of_ge hz.2 hz.1)
  | cons c cs ih =>
    have hh := Bool.and_eq_true_iff.mp hc
    have hh' : c.segment.left.z=start ∧ c.segment.left.z<c.segment.right.z :=
      of_decide_eq_true hh.1
    by_cases hzi : z≤(c.segment.right.z:ℝ)
    · refine ⟨c,List.mem_cons_self,hh'.2,⟨?_,hzi⟩,?_⟩
      · simpa only [hh'.1] using hz.1
      · simp only [referenceField,if_pos hzi]
    · obtain ⟨d,hd,hpos,hmem,he⟩ := ih hh.2 ⟨lt_of_not_ge hzi,hz.2⟩
      exact ⟨d,List.mem_cons_of_mem c hd,hpos,hmem,by
        simpa only [referenceField,if_neg hzi] using he⟩

theorem referenceField_bounded (field : ReferenceFlowCell→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {B : ℝ}
    (hc : referenceFlowCoverCheck start finish cells=true)
    (hb : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|field c t|≤B)
    {z : ℝ} (hz : z∈Ioc (start:ℝ) finish) : |referenceField field cells z|≤B := by
  obtain ⟨c,hmem,hpos,hz',he⟩ := referenceField_selected field hc hz
  rw [he]
  exact hb c hmem _ (c.timeParameter_mem hpos ⟨hz'.1.le,hz'.2⟩)

theorem referenceField_intervalIntegrable (field : ReferenceFlowCell→ℝ→ℝ)
    {start finish : ℚ} {cells : List ReferenceFlowCell} {B : ℝ}
    (horder : start≤finish) (hc : referenceFlowCoverCheck start finish cells=true)
    (hm : ∀ c,Measurable (field c))
    (hb : ∀ c∈cells,∀ t∈Icc (0:ℝ) 1,|field c t|≤B) :
    IntervalIntegrable (referenceField field cells) volume (start:ℝ) finish := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by exact_mod_cast horder)).mpr
  apply (integrable_const B).mono' (referenceField_measurable field hm cells).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with z hz
  simpa only [Real.norm_eq_abs] using referenceField_bounded field hc hb hz

end Transport
end OptimalG.Certificates
