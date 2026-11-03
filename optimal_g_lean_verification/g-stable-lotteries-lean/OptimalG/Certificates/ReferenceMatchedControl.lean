import OptimalG.Certificates.ReferenceMatchedDerivative
import OptimalG.VariationalEarlyCentralMatching

/-! The actual matched rank/derivative fields form controls in the original
essential score-graph support. This treats the early cap and early central
branches separately, with exact primitive matching in the latter. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set MeasureTheory Variational

theorem matched_control_support_ae {lam delta a b : ℝ} {d : LowRankData}
    {G Xi m : ℝ→ℝ} (hd : Admissible lam d) (hdelta : 0≤delta)
    (ha : xLo≤a) (hb : b≤pHi) (hG : Monotone G)
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc a b),0<deriv G r ∧
      d.phi (G r)=m r/deriv G r ∧ (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (c : ReferenceScalarCell)
    (htime : (c.flow.segment.left.z:ℝ)<c.flow.segment.right.z)
    (hR : (c.flow.segment.left.r:ℝ)<c.flow.segment.right.r)
    (hA : (c.flow.segment.left.a:ℝ)<c.flow.segment.right.a)
    (hApiece : c.flow.aPiece.isSome=true)
    (hlate : c.flow.late=true→c.flow.rPiece.isSome=true)
    (hrangeR : c.flow.rPiece.isSome=true →
      Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆ Icc a b)
    (hrangeCap : c.flow.rPiece.isSome=false →
      Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆ Icc pLo a)
    (hrangeA : Icc (c.flow.segment.left.a:ℝ) c.flow.segment.right.a ⊆ Icc a b)
    (hearly : c.flow.late=false→c.flow.rPiece.isSome=true→
      ∀ s∈Icc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z,
        c.flow.segment.rankMap (·.r) s≤c.flow.segment.rankMap (·.a) s) :
    ∀ᵐ s ∂volume.restrict (Icc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z),
      let t := c.flow.timeParameter s
      let r := c.globalMatchedRank true G t
      let a' := c.globalMatchedRank false G t
      let A := m (c.referenceRank false t)/c.matchedDerivative false G t
      let B := m (c.referenceRank true t)/c.matchedDerivative true G t
      (if c.flow.late then ((r,a',r),A,B)∈controlFeatureSupport d
        else ((r,a',a'),A,A)∈controlFeatureSupport d) ∧
      (if c.flow.rPiece.isSome then
        ParameterTransfer.shiftedPrimitive lam d delta r=Xi (c.referenceRank true t)
        else ParameterTransfer.shiftedPrimitive lam d delta r≤
          cap (lam+delta) (ParameterTransfer.scalar d.S delta) (c.referenceRank true t)) ∧
      0<c.matchedDerivative true G t ∧ 0<c.matchedDerivative false G t := by
  have heR (s : ℝ) : c.referenceRank true (c.flow.timeParameter s)=
      c.flow.segment.rankMap (·.r) s := c.referenceRank_timeParameter true s
  have heA (s : ℝ) : c.referenceRank false (c.flow.timeParameter s)=
      c.flow.segment.rankMap (·.a) s := c.referenceRank_timeParameter false s
  cases hl : c.flow.late
  · by_cases hp : c.flow.rPiece.isSome=true
    · have hh := matched_early_central_reference_segment hd ha hb hG hmatch hgood
        c.flow.segment htime hR hA (hrangeR hp) hrangeA (hearly hl hp)
      simpa only [hl,Bool.false_eq_true,if_true,if_false,
        globalMatchedRank,matchedDerivative,rankProfile,rProfile,aProfile,
        hApiece,hp,heR,heA] using hh
    · have hpfalse : c.flow.rPiece.isSome=false := Bool.eq_false_iff.mpr hp
      have hh := matched_early_reference_segment hd hdelta hb hmatch hgood
        c.flow.segment htime hR hA (hrangeCap hpfalse) hrangeA
      filter_upwards [hh] with s hs
      simp only [hl,Bool.false_eq_true,if_true,if_false,
        globalMatchedRank,matchedDerivative,rankProfile,rProfile,aProfile,
        hApiece,hpfalse,heR,heA]
      exact ⟨hs.1,hs.2.1,by norm_num,hs.2.2⟩
  · have hp := hlate hl
    have hh := matched_late_reference_segment hd ha hb hmatch hgood
      c.flow.segment htime hR hA (hrangeR hp) hrangeA
    simpa only [hl,Bool.false_eq_true,if_true,if_false,
      globalMatchedRank,matchedDerivative,rankProfile,rProfile,aProfile,
      hApiece,hp,heR,heA] using hh

end OptimalG.Certificates.Transport.ReferenceScalarCell
