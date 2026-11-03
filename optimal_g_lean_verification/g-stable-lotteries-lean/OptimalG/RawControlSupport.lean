import OptimalG.SignedRationalControl
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Support

/-! Full support of the actual control-domain measure and pointwise bounds by
the signed rational envelope. Boundary controls are included by continuity. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter
open scoped NNReal

theorem controlDomain_convex : Convex ℝ controlDomain := by
  rw [controlDomain_eq_box_inter]
  apply ((convex_Icc pLo pHi).prod ((convex_Icc xLo xHi).prod (convex_Icc xLo xHi))).inter
  intro a ha b hb s t hs ht hst
  change s*a.1+t*b.1 ≤ s*a.2.2+t*b.2.2
  exact add_le_add (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)

theorem controlDomain_interior_nonempty : (interior controlDomain).Nonempty := by
  let box : Set Control := Ioo (0.25 : ℝ) 0.26 ×ˢ (Ioo (0.30 : ℝ) 0.31 ×ˢ Ioo (0.32 : ℝ) 0.33)
  have hbox : box ⊆ controlDomain := by
    intro c hc
    rcases hc with ⟨hp,hx,hy⟩
    change c.1 ∈ Icc pLo pHi ∧ c.2.1 ∈ Icc xLo xHi ∧ c.2.2 ∈ Icc (max xLo c.1) xHi
    norm_num [pLo,pHi,xLo,xHi,mem_Icc,max_le_iff]
    constructor
    · constructor <;> linarith [hp.1,hp.2]
    constructor
    · constructor <;> linarith [hx.1,hx.2]
    constructor
    · constructor <;> linarith [hy.1,hp.2]
    · linarith [hy.2]
  refine ⟨((0.255 : ℝ),(0.305 : ℝ),(0.325 : ℝ)),mem_interior.mpr ?_⟩
  exact ⟨box,hbox,isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo),by norm_num [box]⟩

/-- The measure restricted to the polytope has support at every boundary point
as well as every interior point. -/
theorem controlDomain_subset_support : controlDomain ⊆ controlMeasure.support := by
  have hi : interior controlDomain ⊆ controlMeasure.support := by
    intro c hc
    apply Measure.interior_inter_support
    exact ⟨hc,by simp only [Measure.support_eq_univ,mem_univ]⟩
  have hh := closure_minimal hi controlMeasure.isClosed_support
  rw [controlDomain_convex.closure_interior_eq_closure_of_nonempty_interior
    controlDomain_interior_nonempty,controlDomain_isClosed.closure_eq] at hh
  exact hh

/-- An almost-everywhere lower bound for a continuous control family holds on
the whole closed control domain. -/
theorem le_control_of_ae_le {f : Control → ℝ} {a : ℝ}
    (hf : ContinuousOn f controlDomain) (ha : ∀ᵐ c ∂controlMeasure, a ≤ f c)
    {c : Control} (hc : c ∈ controlDomain) : a ≤ f c := by
  have hclosed : IsClosed {c ∈ controlDomain | a ≤ f c} :=
    controlDomain_isClosed.isClosed_le continuousOn_const hf
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  exact (controlMeasure.support_subset_of_isClosed hclosed (hm.and ha)
    (controlDomain_subset_support hc)).2

theorem raw_scores_bounded {phi : ℝ → ℝ} (hphi : ContinuousOn phi (Icc xLo xHi)) :
    EssentiallyBounded (fun c : Control => phi c.2.1) controlMeasure ∧
      EssentiallyBounded (fun c : Control => phi c.2.2) controlMeasure := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hphi
  have hm : ∀ᵐ c ∂controlMeasure, c ∈ controlDomain := ae_restrict_mem controlDomain_measurable
  refine ⟨⟨B,?_⟩,⟨B,?_⟩⟩
  · exact hm.mono fun c hc => hB c.2.1 hc.2.1
  · exact hm.mono fun c hc => hB c.2.2 ⟨(le_max_left xLo c.1).trans hc.2.2.1,hc.2.2.2⟩

theorem rawControl_continuousOn {lam delta : ℝ} {J phi : ℝ → ℝ}
    (hJ : Continuous J) (hphi : ContinuousOn phi (Icc xLo xHi))
    (hd : 0 < delta) (hdet : ∀ c ∈ controlDomain, delta ≤ rawDet lam J c) (z u : ℝ) :
    ContinuousOn (signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u)
      controlDomain := by
  have hX : ContinuousOn (fun c : Control => phi c.2.1) controlDomain :=
    hphi.comp (by fun_prop) (fun _ hc => hc.2.1)
  have hY : ContinuousOn (fun c : Control => phi c.2.2) controlDomain :=
    hphi.comp (by fun_prop) (fun c hc => ⟨(le_max_left xLo c.1).trans hc.2.2.1,hc.2.2.2⟩)
  have hH : Continuous (fun c : Control => 2*lam-c.2.1) := by fun_prop
  have hk : Continuous (fun c : Control => c.1+c.2.2-lam) := by fun_prop
  have hR : Continuous (fun c : Control => J c.1) := by fun_prop
  have hP : Continuous (fun c : Control => J (1-c.1)) := by fun_prop
  have hK : Continuous (fun c : Control => J (z-c.1)) := by fun_prop
  have hD : Continuous (rawDet lam J) := by unfold rawDet; fun_prop
  have hDne : ∀ c ∈ controlDomain, rawDet lam J c ≠ 0 := fun c hc => ne_of_gt (hd.trans_le (hdet c hc))
  have hA : ContinuousOn (rawAlpha lam J phi) controlDomain :=
    ((hk.continuousOn.mul hX).add (hH.continuousOn.mul hY)).div hD.continuousOn hDne
  have hB : ContinuousOn (rawBeta lam J phi) controlDomain :=
    ((hR.continuousOn.mul hX).add (hP.continuousOn.mul hY)).div hD.continuousOn hDne
  exact ((hA.mul_const u).sub (hB.mul_const (z-lam))).sub (hA.mul hK.continuousOn)

/-- The essential-infimum field lies below every actual rational control,
including controls on the boundary faces of the polytope. -/
theorem rawVectorField_le_control {lam delta : ℝ} {J phi : ℝ → ℝ} {K : ℝ≥0}
    (hJ : LipschitzWith K J) (hphi : ContinuousOn phi (Icc xLo xHi))
    (hd : 0 < delta) (hdet : ∀ c ∈ controlDomain, delta ≤ rawDet lam J c)
    (z u : ℝ) (c : Control) (hc : c ∈ controlDomain) :
    rawVectorField lam J phi z u ≤
      signedControlH lam J (rawAlpha lam J phi) (rawBeta lam J phi) (·.1) z u c := by
  have hs := raw_scores_bounded hphi
  have hab := raw_coefficients_bounded hJ hd hdet hs.1 hs.2
  have hb := signedControlH_bounded (lam := lam) hJ hab.1 hab.2 control_coordinates_bounded.1 z u
  exact (min_le_right _ _).trans (le_control_of_ae_le
    (rawControl_continuousOn hJ.continuous hphi hd hdet z u)
    (ae_essInf_le hb.boundedBelow) hc)

end OptimalG.Variational
