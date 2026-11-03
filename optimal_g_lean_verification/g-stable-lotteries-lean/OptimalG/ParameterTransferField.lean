import OptimalG.ParameterTransferGeometry
import OptimalG.ParameterControlMonotonicity
import OptimalG.VariationalRawPrimitive
import OptimalG.PhaseControlComparison
import OptimalG.PhasePropagation
import Mathlib.Analysis.Normed.MulAction

/-! Upward parameter comparison for the actual essential-infimum field. -/
namespace OptimalG.Variational.ParameterTransfer
open Set MeasureTheory
open scoped NNReal

noncomputable def shiftedPrimitive (lam : ℝ) (d : LowRankData) (delta : ℝ) : ℝ → ℝ :=
  shifted (clippedPrimitive lam d) delta

theorem gain_lipschitz (delta : ℝ) : LipschitzWith ‖delta‖₊ (gain delta) := by
  have hbase : LipschitzWith 1 (fun r : ℝ => max 0 (r-0.38)) := by
    have hh : LipschitzWith 1 (fun r : ℝ => r-0.38) := by
      convert! LipschitzWith.id.sub (LipschitzWith.const (0.38 : ℝ)) using 1 <;> simp
    exact hh.const_max 0
  have hm : LipschitzWith ‖delta‖₊ (fun r : ℝ => delta*max 0 (r-0.38)) := by
    simpa only [Function.comp_def,smul_eq_mul,mul_one] using (lipschitzWith_smul delta).comp hbase
  unfold gain
  convert! (LipschitzWith.const (0.1788*delta)).add hm using 1 <;> simp

theorem shiftedPrimitive_lipschitz {lam : ℝ} {d : LowRankData}
    (h : Admissible lam d) (delta : ℝ) : LipschitzWith (1+‖delta‖₊) (shiftedPrimitive lam d delta) :=
  h.clippedPrimitive_lipschitz.add (gain_lipschitz delta)

theorem shifted_control_values (lam delta : ℝ) (d : LowRankData)
    {c : Control} (hc : c ∈ controlDomain) {z : ℝ} (hz : z ∈ Icc zStart zEnd) :
    shiftedPrimitive lam d delta c.1=primitive lam d c.1+0.1788*delta ∧
      shiftedPrimitive lam d delta (1-c.1)=quadratic lam (1-c.1)-d.S+0.1788*delta+delta*(0.62-c.1) ∧
      shiftedPrimitive lam d delta (z-c.1)=quadratic lam (z-c.1)-d.S+0.1788*delta+delta*(z-c.1-0.38) := by
  obtain ⟨hp,_,_⟩ := control_ranges hc
  obtain ⟨hR,hP,hK⟩ := clippedPrimitive_control_values lam d hc hz
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zStart,zEnd]
  dsimp [shiftedPrimitive,shifted]
  rw [hR,hP,hK,gain_before (by linarith [hp.2] : c.1 ≤ 0.38),
    gain_after (by linarith [hp.2] : (0.38 : ℝ) ≤ 1-c.1),
    gain_after (by linarith [hz'.1,hp.2] : (0.38 : ℝ) ≤ z-c.1)]
  refine ⟨rfl,by ring,by ring⟩

theorem shifted_determinant {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) {c : Control} (hc : c ∈ controlDomain) :
    (0.0519 : ℝ) ≤ rawDet (lam+delta) (shiftedPrimitive lam d delta) c := by
  have hh := admissible_RP_boxes h hLnew hd hc (t := 1) (by norm_num)
  obtain ⟨hR,hP,_⟩ := shifted_control_values lam delta d hc (z := zStart) (by norm_num [zStart,zEnd])
  rw [rawDet,hR,hP]
  have hdet := hh.2.2.1.le
  unfold Certificates.Control.det at hdet
  convert! hdet using 1 <;> simp only [one_mul] <;> ring

theorem shifted_regular {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta)) (hd : 0 ≤ delta) :
    ∃ K : ℝ≥0, (∀ z, LipschitzWith K (rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z)) ∧
      ∀ u, Continuous (fun z => rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z u) := by
  have hs := h.control_basic_bounded
  exact rawVectorField_regular (shiftedPrimitive_lipschitz h delta)
    (by norm_num : (0 : ℝ) < 0.0519) (fun c hc => shifted_determinant h hLnew hd hc) hs.2.2.1 hs.2.2.2.1

theorem control_comparison {lam delta z Y err : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) {c : Control} (hc : c ∈ controlDomain) (hz : z ∈ Icc zStart zEnd)
    (hYlo : quadratic lam z-quadratic lam 1 ≤ Y) (hYhi : Y ≤ quadratic lam z-d.S)
    (hA : 0 ≤ d.phi c.2.1 ∧ d.phi c.2.1 ≤ lam-c.2.1)
    (hB : 0 ≤ d.phi c.2.2 ∧ d.phi c.2.2 ≤ lam-c.2.2)
    (he : err ∈ Icc (0 : ℝ) (0.784*(0.395*delta))) :
    min (lam-z) (controlH lam d z Y c)-(6.19*(0.395*delta)+4.53*err) ≤
      min (lam+delta-z) (signedControlH (lam+delta) (shiftedPrimitive lam d delta)
        (rawAlpha (lam+delta) (shiftedPrimitive lam d delta) d.phi)
        (rawBeta (lam+delta) (shiftedPrimitive lam d delta) d.phi) (·.1) z (Y+0.5738*delta-err) c) := by
  obtain ⟨hp,hx,hy⟩ := control_ranges hc
  have hz' : z ∈ Icc (0.775 : ℝ) 0.875 := by convert! hz using 1 <;> norm_num [zStart,zEnd]
  have hL := h.compact_lambdaRange
  have hK := h.control_K_bounds hc.1 hz hYlo hYhi
  have hR := h.control_R_lower hc.1
  have hP := h.control_P_bounds hc.1
  have hmono := Certificates.Control.parameter_clipped_mono
    (delta := delta) (U := z-lam) (h := 2*lam-c.2.1) (k := c.1+c.2.2-lam)
    (R := primitive lam d c.1) (P := quadratic lam (1-c.1)-d.S)
    (K := quadratic lam (z-c.1)-d.S-Y) (A := d.phi c.2.1) (B := d.phi c.2.2)
    (by exact lt_trans (by norm_num) (h.determinant_sharp hc))
    (by linarith) hP.1 hK.1 (by linarith [hz'.1,hL.2])
    (by linarith [hp.1,hy.1,hx.2]) hA.1 hB.1 hd
  have hU : z-(lam+delta) ∈ Icc (0.21267 : ℝ) 0.313 :=
    ⟨by linarith [hz'.1,hLnew.2],by linarith [hz'.2,hLnew.1]⟩
  have hdp := mul_le_mul_of_nonneg_left
    (show 0.62-c.1 ≤ (0.395 : ℝ) by linarith [hp.1]) hd
  have hdk := mul_le_mul_of_nonneg_left
    (show z-c.1-0.38 ≤ (0.395 : ℝ) by linarith [hz'.2,hp.1]) hd
  have hphase := Certificates.Control.phaseValue_clipped_of_geometry hLnew hp hx hy
    ((le_max_right xLo c.1).trans hc.2.2.1) hU
    (show d.phi c.2.1 ≤ lam+delta-c.2.1 by linarith [hA.2])
    (show d.phi c.2.2 ≤ lam+delta-c.2.2 by linarith [hB.2])
    (eta := 0.1788*delta) (mu := 0.395*delta)
    (dp := delta*(0.62-c.1)) (dk := delta*(z-c.1-0.38))
    (by positivity) (by positivity) he.1 (by nlinarith only [hdp]) (by nlinarith only [hdk])
    (fun t ht => phase_geometry h hLnew hd hc hz' ht hYlo hYhi he)
  have hmono' : min (lam-z) (controlH lam d z Y c) ≤
      min (lam+delta-z) (Certificates.Control.value (z-(lam+delta)) (2*(lam+delta)-c.2.1)
        (c.1+c.2.2-(lam+delta)) (primitive lam d c.1) (quadratic lam (1-c.1)-d.S)
        (quadratic lam (z-c.1)-d.S-Y) (d.phi c.2.1) (d.phi c.2.2)) := by
    rw [controlH_eq_certified_value]
    convert! hmono using 1 <;> ring
  obtain ⟨hRv,hPv,hKv⟩ := shifted_control_values lam delta d hc hz
  rw [rawControl_eq_value,hRv,hPv,hKv]
  rw [show -(z-(lam+delta))=lam+delta-z by ring] at hphase
  have hh := (sub_le_sub_right hmono' (6.19*(0.395*delta)+4.53*err)).trans hphase
  convert! hh using 1 <;> ring

theorem clipped_essInf_comparison_of_le {I : Type*} [MeasurableSpace I]
    {mu : Measure I} [NeZero mu] {f g : I → ℝ} {C D err : ℝ}
    (hCD : C ≤ D) (herr : 0 ≤ err) (hf : EssentiallyBounded f mu) (hg : EssentiallyBounded g mu)
    (hfg : ∀ᵐ i ∂mu, min C (f i)-err ≤ min D (g i)) :
    min C (essInf f mu)-err ≤ min D (essInf g mu) := by
  apply le_min
  · have hh := min_le_left C (essInf f mu)
    linarith
  · apply le_essInf_of_ae_le _ _ hg.boundedAbove.isCoboundedUnder_ge
    filter_upwards [ae_essInf_le hf.boundedBelow,hfg] with i hi hfi
    have hh := min_le_min_left C hi
    have hg' := min_le_right D (g i)
    linarith

theorem field_comparison {lam delta z Y err : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hd : 0 ≤ delta) (hz : z ∈ Icc zStart zEnd)
    (hYlo : quadratic lam z-quadratic lam 1 ≤ Y) (hYhi : Y ≤ quadratic lam z-d.S)
    (he : err ∈ Icc (0 : ℝ) (0.784*(0.395*delta))) :
    vectorField lam d z Y-(6.19*(0.395*delta)+4.53*err) ≤
      rawVectorField (lam+delta) (shiftedPrimitive lam d delta) d.phi z (Y+0.5738*delta-err) := by
  have hs := h.control_basic_bounded
  have hcoeff := raw_coefficients_bounded (shiftedPrimitive_lipschitz h delta)
    (by norm_num : (0 : ℝ) < 0.0519) (fun c hc => shifted_determinant h hLnew hd hc)
    hs.2.2.1 hs.2.2.2.1
  have hb := signedControlH_bounded (lam := lam+delta) (shiftedPrimitive_lipschitz h delta)
    hcoeff.1 hcoeff.2 control_coordinates_bounded.1 z (Y+0.5738*delta-err)
  have herr0 := he.1
  apply clipped_essInf_comparison_of_le (by linarith) (by positivity) (h.controlH_bounded z Y) hb
  filter_upwards [ae_restrict_mem controlDomain_measurable,ae_control_lowRanks _ h.2.2.2.1] with c hc hphi
  exact control_comparison h hLnew hd hc hz hYlo hYhi hphi.1 hphi.2 he

end OptimalG.Variational.ParameterTransfer
