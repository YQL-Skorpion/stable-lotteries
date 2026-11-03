import OptimalG.Certificates.StaticHighFacts
import OptimalG.Certificates.StaticCurveState
import OptimalG.Certificates.StaticCurveControls
import OptimalG.Certificates.StaticLayerControl
import OptimalG.Certificates.StaticLayerCover
import OptimalG.Certificates.SegmentMembership
import OptimalG.Certificates.HighResidualTree
import OptimalG.VariationalFeatureSupport

/-! Finite residuals and a genuine full-cell cover imply all actual supported
control inequalities for the explicit static curve. -/
namespace OptimalG.Certificates.StaticHighData
open Set MeasureTheory StaticSupport
open StaticLow (lam slack)

def prefixResidualCheck (tree : SegmentTree) (p : CubicPiece) : Bool :=
  if StaticHigh.contact≤p.lo then true else tree.residualCheck p lam slack (1/10000000)

private theorem prefix_piece {z : ℝ} (hz : z∈Icc (lam:ℝ) StaticHigh.contact) :
    ∃p∈pieces,p.lo<StaticHigh.contact ∧ z∈Icc (p.lo:ℝ) p.hi ∧
      score z=p.score (z-p.lo) ∧ primitive z=p.primitive (z-p.lo) := by
  by_cases he : z=(StaticHigh.contact:ℝ)
  · subst z
    have hp : piece158∈pieces := by simp [pieces]
    have hr : (StaticHigh.contact:ℝ)∈Icc (piece158.lo:ℝ) piece158.hi := by
      norm_num [piece158,StaticHigh.contact]
    exact ⟨piece158,hp,by norm_num [piece158,StaticHigh.contact],hr,piece_values hp hr⟩
  · have hr : z∈Icc (lam:ℝ) 1 := ⟨hz.1,hz.2.trans (by norm_num [StaticHigh.contact])⟩
    have hf : piece0∈pieces := by simp only [pieces,List.mem_cons_self]
    have hl : piece159∈pieces := by simp [pieces]
    obtain ⟨p,hp,hpr,hs,hf⟩ := HighPieceCover.values trajectory_checked hf hl
      (L:=0) (S:=-(1/2:ℚ)) (r:=z) (by convert! hr using 1 <;> norm_num [piece0,piece159,lam])
    have hlt : (p.lo:ℝ)<StaticHigh.contact := lt_of_le_of_lt hpr.1 (lt_of_le_of_ne hz.2 he)
    refine ⟨p,hp,by exact_mod_cast hlt,hpr,?_,?_⟩
    · simpa only [score,Rat.cast_zero] using hs
    · simpa only [primitive,Rat.cast_zero,Rat.cast_neg] using hf

theorem score_le_node_field {tree : SegmentTree} (htree : tree.check=true)
    (hr : pieces.all (prefixResidualCheck tree)=true)
    {n : LayerNode} (hn : n∈tree.entries) {z : ℝ}
    (hz : z∈Icc (lam:ℝ) StaticHigh.contact) :
    score z≤coefficientField lam slack z (primitive z) n.p n.Cu n.alphau-1/10000000 := by
  obtain ⟨p,hp,hbefore,hpz,hps,hpf⟩ := prefix_piece hz
  have hc := List.all_eq_true.mp hr p hp
  rw [prefixResidualCheck,if_neg (not_le.mpr hbefore)] at hc
  have hb := CubicPiece.highResidual_sound (sub_pos.mpr (HighPieceCover.member_length_pos trajectory_checked hp))
    (SegmentTree.residualCheck_sound htree hc hn) hpz
  rw [hps,hpf]
  convert hb using 1 <;> simp only [coefficientField,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] <;> ring

theorem score_le_control_ae {tree : SegmentTree} {cells : List StaticSupport.ContinuousLayerCell}
    (htree : tree.check=true) (hr : pieces.all (prefixResidualCheck tree)=true)
    (hg : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true)
    (hn : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true)
    (hm : cells.all (fun c=>tree.nodeCheck c.left && tree.nodeCheck c.right)=true)
    (hcover : StaticSupport.continuousCellCoverCheck (1/4) (9/25) cells=true)
    {z : ℝ} (hz : z∈Icc Variational.zStart (StaticHigh.contact:ℝ)) :
    ∀ᵐ q ∂Variational.controlMeasure,
      score z≤Variational.controlH lam Variational.staticLowData z (primitive z) q := by
  have hL : (lam:ℝ)≤z := by norm_num [lam,Variational.zStart] at hz ⊢; linarith [hz.1]
  have hz1 : z≤1 := hz.2.trans (by norm_num [StaticHigh.contact])
  have hbud := StaticCurve.state_sandwich ⟨hL,hz1⟩
  change quadratic lam z-quadratic lam 1≤StaticCurve.primitive z ∧
    StaticCurve.primitive z≤quadratic lam z-slack at hbud
  rw [StaticCurve.high_primitive hL] at hbud
  have hz' : z∈Icc Variational.zStart Variational.zEnd :=
    ⟨hz.1,hz.2.trans (by norm_num [StaticHigh.contact,Variational.zEnd])⟩
  filter_upwards [StaticSupport.continuousCellCoverCheck_controls hcover,
    ae_restrict_mem Variational.controlDomain_measurable] with q hcell hdom
  obtain ⟨c,hc,t,ht,hparam⟩ := hcell
  have he : c.pPoly.eval t=q.1 := by rw [StaticSupport.ContinuousLayerCell.pPoly_eval]; exact hparam.symm
  have hctl : (c.pPoly.eval t,q.2.1,q.2.2)∈Variational.controlDomain := by
    simpa only [he,Prod.eta] using hdom
  have hbound := Variational.StaticLayerCell.node_fields_lower_controlH
    (List.all_eq_true.mp hg c hc) (List.all_eq_true.mp hn c hc) ht hctl hz' hbud.1 hbud.2
  have hm' := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hm c hc)
  have hl := score_le_node_field htree hr (SegmentTree.nodeCheck_sound hm'.1) ⟨hL,hz.2⟩
  have hr' := score_le_node_field htree hr (SegmentTree.nodeCheck_sound hm'.2) ⟨hL,hz.2⟩
  have hmin : score z+1/10000000≤
      min (coefficientField lam slack z (primitive z) c.left.p c.left.Cu c.left.alphau)
        (coefficientField lam slack z (primitive z) c.right.p c.right.Cu c.right.alphau) :=
    le_min (by linarith only [hl]) (by linarith only [hr'])
  have heq : (c.pPoly.eval t,q.2.1,q.2.2)=q := by rw [he]
  rw [heq] at hbound
  linarith only [hmin,hbound]

theorem supported_controls_of_certificates {tree : SegmentTree} {cells : List StaticSupport.ContinuousLayerCell}
    (htree : tree.check=true) (hr : pieces.all (prefixResidualCheck tree)=true)
    (hg : cells.all StaticSupport.ContinuousLayerCell.geometryCheck=true)
    (hn : cells.all StaticSupport.ContinuousLayerCell.fastNumericCheck=true)
    (hm : cells.all (fun c=>tree.nodeCheck c.left && tree.nodeCheck c.right)=true)
    (hcover : StaticSupport.continuousCellCoverCheck (1/4) (9/25) cells=true) :
    ∀z∈Icc Variational.zStart 1,∀v∈Variational.controlFeatureSupport Variational.staticLowData,
      StaticCurve.score z≤Variational.featureH Variational.staticLow_admissible z
        (curvePrimitive StaticCurve.score z) v := by
  apply StaticCurve.all_controls
  intro z hz v hv
  have hL : (lam:ℝ)≤z := by norm_num [lam,Variational.zStart] at hz ⊢; linarith [hz.1]
  have hlow : score z≤essInf (Variational.controlH lam Variational.staticLowData z (primitive z))
      Variational.controlMeasure := by
    exact le_essInf_of_ae_le _ (score_le_control_ae htree hr hg hn hm hcover hz)
      (Variational.staticLow_admissible.controlH_bounded z (primitive z)).boundedAbove.isCoboundedUnder_ge
  have hh := hlow.trans (Variational.staticLow_admissible.essInf_le_featureH z (primitive z) hv)
  rw [StaticCurve.high_score hL]
  change score z≤Variational.featureH Variational.staticLow_admissible z (StaticCurve.primitive z) v
  rw [StaticCurve.high_primitive hL]
  exact hh

end OptimalG.Certificates.StaticHighData
