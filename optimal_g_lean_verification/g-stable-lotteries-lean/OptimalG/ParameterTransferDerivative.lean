import OptimalG.ParameterTransferLowData

/-! The original measurable score is the actual derivative of the shifted
primitive almost everywhere on all ranks used by the control family. -/
namespace OptimalG.Variational.ParameterTransfer
open Set MeasureTheory Filter
open scoped Topology

theorem shifted_low_hasDerivAt_ae {lam delta : ℝ} {d : LowRankData} (h : Admissible lam d) :
    ∀ᵐ r ∂volume.restrict (Icc ell xHi),HasDerivAt (shiftedPrimitive lam d delta) (d.phi r) r := by
  have hle : ell ≤ tEnd := by norm_num [ell,tEnd]
  have hi := (h.intervalIntegrable le_rfl hle le_rfl).ae_hasDerivAt_integral
  rw [← restrict_Ioo_eq_restrict_Icc]
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hi] with r hdr hr
  have hrell : ell < r := hr.1
  have hrt : r < tEnd := hr.2.trans (by norm_num [xHi,tEnd])
  have hri : r ∈ uIcc ell tEnd := by
    rw [uIcc_of_le hle]
    exact ⟨hrell.le,hrt.le⟩
  have hd := (hdr hri ell (by simp [uIcc_of_le hle,hle])).const_add (cap lam d.S ell)
  have hd' := hd.add_const (0.1788*delta)
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hrell hr.2] with t ht
  have htI : t ∈ Icc pLo zStart :=
    ⟨(by norm_num [pLo,ell] : pLo ≤ ell).trans ht.1.le,
      ht.2.le.trans (by norm_num [xHi,zStart])⟩
  rw [shiftedPrimitive_eq lam delta d htI]
  dsimp [shifted]
  rw [primitive_eq_lowPrimitive ⟨ht.1.le,ht.2.le.trans (by norm_num [xHi,tEnd])⟩,
    gain_before (by convert! ht.2.le using 1 <;> norm_num [xHi])]
  rfl

theorem shifted_low_score_bounds {lam delta : ℝ} {d : LowRankData}
    (h : Admissible lam d) (hd : 0 ≤ delta) :
    ∀ᵐ r ∂volume.restrict (Icc ell xHi),
      HasDerivAt (shiftedPrimitive lam d delta) (d.phi r) r ∧ 0 ≤ d.phi r ∧ d.phi r ≤ lam+delta-r := by
  have hb : ∀ᵐ r ∂volume.restrict (Icc ell xHi),0 ≤ d.phi r ∧ d.phi r ≤ lam-r :=
    ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc le_rfl (by norm_num [xHi,tEnd])) h.2.2.2.1
  filter_upwards [shifted_low_hasDerivAt_ae h,hb] with r hder hscore
  exact ⟨hder,hscore.1,by linarith [hscore.2]⟩

end OptimalG.Variational.ParameterTransfer
