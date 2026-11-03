import OptimalG.VariationalTransferredSupport

/-! The early control branch can persist after both reference ranks enter
the central interval. Both ranks are then transported. Its r entropy weight
is still zero, but its positional variation need not vanish. -/
namespace OptimalG.Variational
open Set MeasureTheory Certificates.Transport

theorem matched_early_central_reference_segment {lam delta a b : ℝ} {d : LowRankData}
    {G Xi m : ℝ→ℝ} (hd : Admissible lam d) (ha : xLo≤a) (hb : b≤pHi)
    (hG : Monotone G)
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc a b),0<deriv G r ∧
      d.phi (G r)=m r/deriv G r ∧ (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (seg : ReferenceSegment)
    (htime : (seg.left.z:ℝ)<seg.right.z)
    (hR : (seg.left.r:ℝ)<seg.right.r) (hA : (seg.left.a:ℝ)<seg.right.a)
    (hrangeR : Icc (seg.left.r:ℝ) seg.right.r ⊆ Icc a b)
    (hrangeA : Icc (seg.left.a:ℝ) seg.right.a ⊆ Icc a b)
    (horder : ∀ s∈Icc (seg.left.z:ℝ) seg.right.z,
      seg.rankMap (·.r) s≤seg.rankMap (·.a) s) :
    ∀ᵐ s ∂volume.restrict (Icc (seg.left.z:ℝ) seg.right.z),
      ((G (seg.rankMap (·.r) s),G (seg.rankMap (·.a) s),G (seg.rankMap (·.a) s)),
        m (seg.rankMap (·.a) s)/deriv G (seg.rankMap (·.a) s),
        m (seg.rankMap (·.a) s)/deriv G (seg.rankMap (·.a) s))∈controlFeatureSupport d ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G (seg.rankMap (·.r) s))=
        Xi (seg.rankMap (·.r) s) ∧
      0<deriv G (seg.rankMap (·.r) s) ∧ 0<deriv G (seg.rankMap (·.a) s) := by
  have hgR := ae_reference_segment_pullback seg (·.r) htime hR hrangeR hgood
  have hgA := ae_reference_segment_pullback seg (·.a) htime hA hrangeA hgood
  filter_upwards [hgR,hgA,ae_restrict_mem measurableSet_Icc] with s hsR hsA hs
  have hmR := hmatch _ (hrangeR (reference_rankMap_bounds seg (·.r) htime hR hs))
  have hp : G (seg.rankMap (·.r) s)∈Icc pLo pHi :=
    ⟨((by norm_num [pLo,xLo] : pLo≤xLo).trans ha).trans hmR.1.1,hmR.1.2.trans hb⟩
  have hfeature := hd.feature_mem_support_of_rankScores hp hsA.2.2 hsA.2.2
    (hG (horder s hs))
  rw [hsA.2.1] at hfeature
  exact ⟨hfeature,hmR.2,hsR.1,hsA.1⟩

end OptimalG.Variational
