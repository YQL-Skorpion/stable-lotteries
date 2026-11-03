import OptimalG.Certificates.ReferenceLowCurve
import OptimalG.VariationalReferenceGauge
import OptimalG.VariationalTransferredSupport

/-! The checked low reference and scalar gauge produce the actual increasing
primitive used by rank transport. Its endpoint identities and matching are
proved from the polynomial joins, not supplied as a separate reference model. -/
namespace OptimalG.Certificates.Transport.ReferenceData
open Set MeasureTheory Function

noncomputable def transportPrimitive (d : ReferenceData) (S : ℝ) (r : ℝ) : ℝ :=
  d.lowPrimitive r+(S-d.slack)*d.globalGauge r

noncomputable def transportScore (d : ReferenceData) (S : ℝ) (r : ℝ) : ℝ :=
  d.lowScore r+(S-d.slack)*d.globalGaugeDerivative r

def tailFrameCheck (d : ReferenceData) : Bool :=
  d.pieces.all (fun p=>decide (p.hi≤d.rightContact))

theorem lowPrimitive_cap (d : ReferenceData) {r : ℝ} (hr : r≤d.leftContact) :
    d.lowPrimitive r=cap d.lam d.slack r := by
  simp only [lowPrimitive,capCubicPrimitive,if_pos hr]

theorem low_tail_values (d : ReferenceData)
    (hlow : d.lowCurveCheck=true) (hgauge : d.gaugeCheck=true)
    (htail : d.tailFrameCheck=true) {r : ℝ} (hr : (d.rightContact:ℝ)≤r) :
    d.lowScore r=(d.lam:ℝ)-r ∧ d.lowPrimitive r=quadratic d.lam r-d.slack := by
  have horder : (d.leftContact:ℝ)<d.rightContact := by
    exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp hgauge).1).1
  have hlocal (x : ℝ) (hx : x∈Ioi (d.rightContact:ℝ)) :
      d.lowScore x=(d.lam:ℝ)-x ∧ d.lowPrimitive x=quadratic d.lam x-d.slack := by
    have hp : ∀ p∈d.pieces,(p.hi:ℝ)<x := by
      intro p hm
      have hh : p.hi≤d.rightContact := of_decide_eq_true (List.all_eq_true.mp htail p hm)
      exact (show (p.hi:ℝ)≤d.rightContact by exact_mod_cast hh).trans_lt hx
    have ht := cubic_tail_values d.lam d.slack x d.pieces hp
    have hnot : ¬x≤(d.leftContact:ℝ) := not_le.mpr (horder.trans hx)
    simpa only [lowPrimitive,lowScore,capCubicPrimitive,capCubicScore,if_neg hnot,
      quadratic] using ht
  have hscore : EqOn d.lowScore (fun x=>(d.lam:ℝ)-x) (Ioi (d.rightContact:ℝ)) :=
    fun x hx=>(hlocal x hx).1
  have hprimitive : EqOn d.lowPrimitive (fun x=>quadratic d.lam x-d.slack)
      (Ioi (d.rightContact:ℝ)) := fun x hx=>(hlocal x hx).2
  have hs := hscore.closure (d.lowScore_continuous hlow) (by fun_prop)
  have hp := hprimitive.closure (d.lowPrimitive_continuous hlow)
    (by unfold quadratic; fun_prop)
  rw [closure_Ioi] at hs hp
  exact ⟨hs hr,hp hr⟩

theorem transportPrimitive_hasDerivAt (d : ReferenceData)
    (hlow : d.lowCurveCheck=true) (hgauge : d.gaugeCheck=true) (S r : ℝ) :
    HasDerivAt (d.transportPrimitive S) (d.transportScore S r) r :=
  warpedReference_hasDerivAt hgauge (d.lowPrimitive_hasDerivAt hlow r)

theorem transportPrimitive_endpoints (d : ReferenceData)
    (hlow : d.lowCurveCheck=true) (hgauge : d.gaugeCheck=true)
    (htail : d.tailFrameCheck=true) (S : ℝ) :
    d.transportPrimitive S d.leftContact=cap d.lam S d.leftContact ∧
    d.transportPrimitive S d.rightContact=quadratic d.lam d.rightContact-S := by
  refine ⟨warpedReference_cap le_rfl (d.lowPrimitive_cap le_rfl),?_⟩
  exact warpedReference_tail hgauge le_rfl (d.low_tail_values hlow hgauge htail le_rfl).2

/-- The reference polynomial checks and its actual shifted-score floor yield
an original-score-graph matching for every upward-transferred competitor. -/
theorem transferred_matching_exists (ref : ReferenceData)
    {lam delta : ℝ} {d : Variational.LowRankData}
    (hd : Variational.Admissible lam d) (hdelta : 0≤delta)
    (hparam : (ref.lam:ℝ)=lam+delta)
    (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    (htail : ref.tailFrameCheck=true)
    (hleft : Variational.xLo≤ref.leftContact) (hright : (ref.rightContact:ℝ)≤Variational.pHi)
    (hscore : ∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
      (1/5:ℝ)≤ref.transportScore (Variational.ParameterTransfer.scalar d.S delta) r) :
    ∃ G : StieltjesFunction ℝ,leftLim G ref.leftContact=(ref.leftContact:ℝ) ∧
      (∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
        G r∈Icc (ref.leftContact:ℝ) ref.rightContact ∧
        Variational.ParameterTransfer.shiftedPrimitive lam d delta (G r)=
          ref.transportPrimitive (Variational.ParameterTransfer.scalar d.S delta) r) ∧
      (∀ᵐ r ∂volume.restrict (Icc (ref.leftContact:ℝ) ref.rightContact),
        HasDerivAt G (deriv G r) r ∧ 0<deriv G r ∧ (3/5:ℝ)≤deriv G r ∧
        d.phi (G r)=ref.transportScore (Variational.ParameterTransfer.scalar d.S delta) r/deriv G r ∧
        (G r,d.phi (G r))∈Variational.rankScoreSupport d.phi) ∧
      ∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
        (G r-r)^2≤2*((ref.rightContact:ℝ)-ref.leftContact)*
          Variational.matchingVariation G ref.leftContact ref.rightContact := by
  have hab : (ref.leftContact:ℝ)≤ref.rightContact := by
    exact_mod_cast (of_decide_eq_true (Bool.and_eq_true_iff.mp hgauge).1).1.le
  have he := ref.transportPrimitive_endpoints hlow hgauge htail
    (Variational.ParameterTransfer.scalar d.S delta)
  rw [hparam] at he
  have hh := Variational.transferred_reference_matching_support hd hdelta hab hleft hright
    (by norm_num : (0:ℝ)<1/5) he.1 he.2
    (fun r _=>ref.transportPrimitive_hasDerivAt hlow hgauge _ r)
    (fun r hr=>hscore r ⟨hr.1.le,hr.2.le⟩)
  convert! hh using 1 <;> norm_num

end OptimalG.Certificates.Transport.ReferenceData
