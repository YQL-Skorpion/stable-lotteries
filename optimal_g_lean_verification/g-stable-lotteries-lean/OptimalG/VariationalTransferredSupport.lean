import OptimalG.VariationalTransferredMatching
import OptimalG.VariationalMatchedSupports

/-! The genuine transferred primitive admits a Stieltjes matching whose
score values belong to the original essential score graph. Pullback along the
checked affine reference segments supplies the actual early/late controls. -/
namespace OptimalG.Variational
open Set MeasureTheory Function Certificates.Transport
open scoped NNReal

theorem transferred_reference_matching_support {lam delta a b m0 : ℝ}
    {d : LowRankData} {Xi m : ℝ → ℝ}
    (hd : Admissible lam d) (hdelta : 0≤delta)
    (hab : a≤b) (ha : xLo≤a) (hb : b≤pHi) (hm0 : 0<m0)
    (hleft : Xi a=cap (lam+delta) (ParameterTransfer.scalar d.S delta) a)
    (hright : Xi b=quadratic (lam+delta) b-ParameterTransfer.scalar d.S delta)
    (hXid : ∀ r∈Icc a b,HasDerivAt Xi (m r) r)
    (hm : ∀ r∈Ioo a b,m0≤m r) :
    ∃ G : StieltjesFunction ℝ,leftLim G a=a ∧
      (∀ r∈Icc a b,G r∈Icc a b ∧
        ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r) ∧
      (∀ᵐ r ∂volume.restrict (Icc a b),HasDerivAt G (deriv G r) r ∧
        0<deriv G r ∧ 3*m0≤deriv G r ∧ d.phi (G r)=m r/deriv G r ∧
        (G r,d.phi (G r))∈rankScoreSupport d.phi) ∧
      ∀ r∈Icc a b,(G r-r)^2≤2*(b-a)*matchingVariation G a b := by
  have hal : ell≤a := (by norm_num [ell,xLo] : ell≤xLo).trans ha
  have hbx : b≤xHi := hb.trans (by norm_num [pHi,xHi])
  obtain ⟨G,hGl,hmatch,hder,hvar⟩ := transferred_reference_matching hd hdelta
    hab hal hbx hm0 hleft hright hXid hm
  have hsupp := matched_rankScore_support_ae hd hm0 (Icc_subset_Icc ha hbx)
    ((ParameterTransfer.shifted_low_monotone hd hdelta).mono
      (Icc_subset_Icc ((by norm_num [pLo,xLo] : pLo≤xLo).trans ha)
        (hb.trans (by norm_num [pHi,tEnd]))))
    ((transferred_low_lipschitz hd).mono (Icc_subset_Icc hal hbx))
    (reference_primitive_strictMono hm0 hXid hm)
    (reference_primitive_lower_increment hXid hm) hmatch
  refine ⟨G,hGl,hmatch,?_,hvar⟩
  filter_upwards [hder,hsupp] with r hr hs
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2,hs⟩

/-- Both matched rank coordinates give a genuine late control almost
 everywhere in time, with the exact matched primitive and derivative ratios. -/
theorem matched_late_reference_segment {lam delta a b : ℝ} {d : LowRankData}
    {G Xi m : ℝ → ℝ} (hd : Admissible lam d) (ha : xLo≤a) (hb : b≤pHi)
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc a b),0<deriv G r ∧
      d.phi (G r)=m r/deriv G r ∧ (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (seg : ReferenceSegment)
    (htime : (seg.left.z:ℝ)<seg.right.z)
    (hR : (seg.left.r:ℝ)<seg.right.r) (hA : (seg.left.a:ℝ)<seg.right.a)
    (hrangeR : Icc (seg.left.r:ℝ) seg.right.r ⊆ Icc a b)
    (hrangeA : Icc (seg.left.a:ℝ) seg.right.a ⊆ Icc a b) :
    ∀ᵐ s ∂volume.restrict (Icc (seg.left.z:ℝ) seg.right.z),
      ((G (seg.rankMap (·.r) s),G (seg.rankMap (·.a) s),G (seg.rankMap (·.r) s)),
        m (seg.rankMap (·.a) s)/deriv G (seg.rankMap (·.a) s),
        m (seg.rankMap (·.r) s)/deriv G (seg.rankMap (·.r) s))∈controlFeatureSupport d ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G (seg.rankMap (·.r) s))=
        Xi (seg.rankMap (·.r) s) ∧
      0<deriv G (seg.rankMap (·.r) s) ∧ 0<deriv G (seg.rankMap (·.a) s) := by
  have hgR := ae_reference_segment_pullback seg (·.r) htime hR hrangeR hgood
  have hgA := ae_reference_segment_pullback seg (·.a) htime hA hrangeA hgood
  filter_upwards [hgR,hgA,ae_restrict_mem measurableSet_Icc] with s hsR hsA hs
  have hmR := hmatch _ (hrangeR (reference_rankMap_bounds seg (·.r) htime hR hs))
  have hmA := hmatch _ (hrangeA (reference_rankMap_bounds seg (·.a) htime hA hs))
  have hfeature := matched_late_feature_mem_support hd ha hb hmR.1 hmA.1 hsR.2.2 hsA.2.2
  rw [hsR.2.1,hsA.2.1] at hfeature
  exact ⟨hfeature,hmR.2,hsR.1,hsA.1⟩

/-- The early mass coordinate stays fixed below the matched interval. Its
primitive is bounded by the cap; only the second rank is transported. -/
theorem matched_early_reference_segment {lam delta a b : ℝ} {d : LowRankData}
    {G Xi m : ℝ → ℝ} (hd : Admissible lam d) (hdelta : 0≤delta) (hb : b≤pHi)
    (hmatch : ∀ r∈Icc a b,G r∈Icc a b ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc a b),0<deriv G r ∧
      d.phi (G r)=m r/deriv G r ∧ (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (seg : ReferenceSegment)
    (htime : (seg.left.z:ℝ)<seg.right.z)
    (hR : (seg.left.r:ℝ)<seg.right.r) (hA : (seg.left.a:ℝ)<seg.right.a)
    (hrangeR : Icc (seg.left.r:ℝ) seg.right.r ⊆ Icc pLo a)
    (hrangeA : Icc (seg.left.a:ℝ) seg.right.a ⊆ Icc a b) :
    ∀ᵐ s ∂volume.restrict (Icc (seg.left.z:ℝ) seg.right.z),
      ((seg.rankMap (·.r) s,G (seg.rankMap (·.a) s),G (seg.rankMap (·.a) s)),
        m (seg.rankMap (·.a) s)/deriv G (seg.rankMap (·.a) s),
        m (seg.rankMap (·.a) s)/deriv G (seg.rankMap (·.a) s))∈controlFeatureSupport d ∧
      ParameterTransfer.shiftedPrimitive lam d delta (seg.rankMap (·.r) s)≤
        cap (lam+delta) (ParameterTransfer.scalar d.S delta) (seg.rankMap (·.r) s) ∧
      0<deriv G (seg.rankMap (·.a) s) := by
  have hgA := ae_reference_segment_pullback seg (·.a) htime hA hrangeA hgood
  filter_upwards [hgA,ae_restrict_mem measurableSet_Icc] with s hsA hs
  have hmA := hmatch _ (hrangeA (reference_rankMap_bounds seg (·.a) htime hA hs))
  have hr := hrangeR (reference_rankMap_bounds seg (·.r) htime hR hs)
  have hab : a≤b := hmA.1.1.trans hmA.1.2
  have hrp : seg.rankMap (·.r) s∈Icc pLo pHi := ⟨hr.1,hr.2.trans (hab.trans hb)⟩
  have hfeature := matched_early_feature_mem_support hd hrp hr.2 hmA.1 hsA.2.2
  rw [hsA.2.1] at hfeature
  exact ⟨hfeature,ParameterTransfer.shifted_cap_bound hd hdelta
    ⟨hrp.1,hrp.2.trans (by norm_num [pHi,tEnd])⟩,hsA.1⟩

end OptimalG.Variational
