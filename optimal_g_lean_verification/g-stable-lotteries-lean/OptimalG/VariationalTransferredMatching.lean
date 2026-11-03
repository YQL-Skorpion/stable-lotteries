import OptimalG.ParameterTransfer
import OptimalG.VariationalReferenceGrowth

/-! The actual B.2 competitor admits the B.4 Stieltjes rank matching. The
reference endpoint equalities and positive derivative are the only reference
inputs; all competing-primitive conditions follow from admissibility. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter Function
open scoped Topology NNReal

 theorem transferred_low_lipschitz {lam delta : ℝ} {d : LowRankData}
    (hd : Admissible lam d) :
    LipschitzOnWith (1/3 : ℝ≥0) (ParameterTransfer.shiftedPrimitive lam d delta) (Icc ell xHi) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro r hr s hs
  have hr' : r ∈ Icc ell tEnd := ⟨hr.1,hr.2.trans (by norm_num [xHi,tEnd])⟩
  have hs' : s ∈ Icc ell tEnd := ⟨hs.1,hs.2.trans (by norm_num [xHi,tEnd])⟩
  rw [Real.dist_eq,ParameterTransfer.shifted_low_increment hd hs hr,← hd.lowPrimitive_sub hs' hr',
    ← Real.dist_eq]
  exact hd.lowPrimitive_lipschitz.dist_le_mul r hr' s hs'

 theorem transferred_reference_matching {lam delta a b m0 : ℝ} {d : LowRankData}
    {Xi m : ℝ → ℝ}
    (hd : Admissible lam d) (hdelta : 0 ≤ delta)
    (hab : a ≤ b) (ha : ell ≤ a) (hb : b ≤ xHi) (hm0 : 0 < m0)
    (hleft : Xi a=cap (lam+delta) (ParameterTransfer.scalar d.S delta) a)
    (hright : Xi b=quadratic (lam+delta) b-ParameterTransfer.scalar d.S delta)
    (hXid : ∀ r ∈ Icc a b, HasDerivAt Xi (m r) r)
    (hm : ∀ r ∈ Ioo a b, m0 ≤ m r) :
    ∃ G : StieltjesFunction ℝ, leftLim G a=a ∧
      (∀ r ∈ Icc a b, G r ∈ Icc a b ∧ ParameterTransfer.shiftedPrimitive lam d delta (G r)=Xi r) ∧
      (∀ᵐ r ∂volume.restrict (Icc a b), HasDerivAt G (deriv G r) r ∧
        0 < deriv G r ∧ 3*m0 ≤ deriv G r ∧ d.phi (G r)=m r/deriv G r) ∧
      ∀ r ∈ Icc a b, (G r-r)^2 ≤ 2*(b-a)*matchingVariation G a b := by
  have hsub : Icc a b ⊆ Icc ell xHi := Icc_subset_Icc ha hb
  have hsubLow : Icc a b ⊆ Icc pLo tEnd := Icc_subset_Icc
    ((by norm_num [pLo,ell] : pLo ≤ ell).trans ha)
    (hb.trans (by norm_num [xHi,tEnd]))
  have haLow := hsubLow (show a ∈ Icc a b from ⟨le_rfl,hab⟩)
  have hbLow := hsubLow (show b ∈ Icc a b from ⟨hab,le_rfl⟩)
  have hJder : ∀ᵐ s ∂volume, s ∈ Icc a b →
      HasDerivAt (ParameterTransfer.shiftedPrimitive lam d delta) (d.phi s) s ∧
        0 ≤ d.phi s ∧ d.phi s ≤ ((1/3 : ℝ≥0):ℝ) := by
    apply (ae_restrict_iff' measurableSet_Icc).mp
    have hlow := ae_restrict_of_ae_restrict_of_subset hsub
      (ParameterTransfer.shifted_low_score_bounds hd hdelta)
    have hnorm := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc ha (hb.trans (by norm_num [xHi,tEnd]))) hd.phi_norm_bound
    filter_upwards [hlow,hnorm] with s hs hn
    refine ⟨hs.1,hs.2.1,?_⟩
    have hscore := (le_abs_self (d.phi s)).trans (by simpa only [Real.norm_eq_abs] using hn)
    simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hscore
  have hh := exists_measured_primitive_matching_of_deriv (Xi:=Xi) hab hm0
    (show 0 < ((1/3 : ℝ≥0):ℝ) by positivity)
    ((ParameterTransfer.shifted_low_monotone hd hdelta).mono hsubLow)
    ((transferred_low_lipschitz hd).mono hsub)
    (by
      rw [hleft]
      exact ParameterTransfer.shifted_cap_bound hd hdelta haLow)
    (by
      rw [hright]
      exact ParameterTransfer.shifted_root_bound hd hdelta
        ⟨hbLow.1,hbLow.2.trans (by norm_num [tEnd,zStart])⟩)
    hJder hXid hm
  convert! hh using 1 <;> norm_num [div_eq_mul_inv,mul_comm]

end OptimalG.Variational
