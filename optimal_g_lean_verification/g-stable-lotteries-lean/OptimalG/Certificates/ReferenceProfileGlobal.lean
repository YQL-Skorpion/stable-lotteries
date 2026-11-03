import OptimalG.Certificates.ReferenceProfileCell
import OptimalG.Certificates.ReferenceLowCurve
import OptimalG.VariationalReferenceGauge

/-! Finite profile boxes describe the single actual low reference and its
C¹ gauge. A checked rank cover makes the shifted-score bound global. -/
namespace OptimalG.Certificates
open Set
namespace ReferenceProfileCell

def coverCheck (start finish : ℚ) : List ReferenceProfileCell→Bool
  | [] => decide (start=finish)
  | c::cs => decide (c.lo=start ∧ c.lo<c.hi) && coverCheck c.hi finish cs

theorem coverCheck_sound {start finish : ℚ} {cs : List ReferenceProfileCell}
    (hc : coverCheck start finish cs=true) (horder : start<finish)
    {r : ℝ} (hr : r∈Icc (start:ℝ) finish) :
    ∃ c∈cs,r∈Icc (c.lo:ℝ) c.hi := by
  induction cs generalizing start with
  | nil =>
    have he : start=finish := of_decide_eq_true hc
    exact False.elim (horder.ne he)
  | cons c cs ih =>
    obtain ⟨hh,ht⟩ := Bool.and_eq_true_iff.mp hc
    have hg : c.lo=start ∧ c.lo<c.hi := of_decide_eq_true hh
    by_cases he : r≤(c.hi:ℝ)
    · exact ⟨c,List.mem_cons_self,by simpa only [hg.1,mem_Icc] using And.intro hr.1 he⟩
    · have hgt : (c.hi:ℝ)<r := lt_of_not_ge he
      have htail : c.hi<finish := by exact_mod_cast hgt.trans_le hr.2
      obtain ⟨d,hd,hdr⟩ := ih ht htail ⟨hgt.le,hr.2⟩
      exact ⟨d,List.mem_cons_of_mem c hd,hdr⟩

def frameCheck (d : Transport.ReferenceData) (c : ReferenceProfileCell) : Bool :=
  decide (c.lam=d.lam ∧ c.slack=d.slack ∧ c.contact=d.leftContact ∧
    c.endContact=d.rightContact ∧ c.gauge=d.gauge ∧ c.gaugeDerivative=d.gaugeDerivative ∧
    c.hi≤d.rightContact) &&
  Transport.ReferenceFlowCell.localProfileCheck d.leftContact d.pieces c.piece c.lo c.hi

theorem frameCheck_values (d : Transport.ReferenceData)
    (hlow : d.lowCurveCheck=true) (hgauge : d.gaugeCheck=true)
    (c : ReferenceProfileCell) (hc : c.frameCheck d=true) {r : ℝ}
    (hr : r∈Icc (c.lo:ℝ) c.hi) :
    Transport.ReferenceFlowCell.localScore c.lam c.slack c.piece r=d.lowScore r ∧
    Transport.ReferenceFlowCell.localPrimitive c.lam c.slack c.piece r=d.lowPrimitive r ∧
    c.localGauge r=d.globalGauge r ∧ c.localGaugeDerivative r=d.globalGaugeDerivative r := by
  obtain ⟨hf,hgeom⟩ := Bool.and_eq_true_iff.mp hc
  have hframe : c.lam=d.lam ∧ c.slack=d.slack ∧ c.contact=d.leftContact ∧
      c.endContact=d.rightContact ∧ c.gauge=d.gauge ∧ c.gaugeDerivative=d.gaugeDerivative ∧
      c.hi≤d.rightContact := of_decide_eq_true hf
  rcases hframe with ⟨hl,hs,hc0,hc1,hg,hd,hh⟩
  obtain ⟨_,hcurve,hjoin0,hjoin1⟩ := d.lowCurveCheck_joins hlow
  have hscore := trajectoryCheck_continuousScore d.lam d.slack d.pieces hcurve
  have hprimitive : Continuous (cubicPrimitive d.lam d.slack d.pieces) :=
    continuous_iff_continuousAt.mpr (fun x =>
      (trajectoryCheck_hasDerivAt d.lam d.slack d.pieces hcurve x).continuousAt)
  have hp := Transport.ReferenceFlowCell.localProfileCheck_values hgeom hscore hprimitive
    ⟨hjoin0,hjoin1⟩ hr
  refine ⟨by simpa only [hl,hs,Transport.ReferenceData.lowScore] using hp.1,
    by simpa only [hl,hs,Transport.ReferenceData.lowPrimitive] using hp.2,?_,?_⟩
  all_goals cases hpiece : c.piece with
  | none =>
    have hq : c.lo≤c.hi ∧ c.hi≤d.leftContact := by
      simpa only [Transport.ReferenceFlowCell.localProfileCheck,hpiece,decide_eq_true_eq] using hgeom
    have hrc : r≤(d.leftContact:ℝ) := hr.2.trans (by exact_mod_cast hq.2)
    first
    | simpa only [localGauge,hpiece,hl] using (d.globalGauge_cap hrc).symm
    | simpa only [localGaugeDerivative,hpiece,hl] using (d.globalGaugeDerivative_cap hrc).symm
  | some p =>
    have hq : (c.lo≤c.hi ∧ d.leftContact≤c.lo ∧ p.lo≤c.lo ∧ c.hi≤p.hi ∧ p.lo<p.hi) ∧
        cubicLookupCheck p d.pieces=true := by
      simpa only [Transport.ReferenceFlowCell.localProfileCheck,hpiece,Bool.and_eq_true_iff,
        decide_eq_true_eq] using hgeom
    have hrc : r∈Icc (d.leftContact:ℝ) d.rightContact :=
      ⟨(show (d.leftContact:ℝ)≤c.lo by exact_mod_cast hq.1.2.1).trans hr.1,
        hr.2.trans (by exact_mod_cast hh)⟩
    first
    | simpa only [localGauge,hpiece,hg,hc0,hc1,Transport.ReferenceData.centralGauge]
        using (d.globalGauge_central hgauge hrc).symm
    | simpa only [localGaugeDerivative,hpiece,hd,hc0,hc1,Transport.ReferenceData.centralGaugeDerivative]
        using (d.globalGaugeDerivative_central hgauge hrc).symm

/-- The coarse derivative floor is obtained from the finite profile and rank
cover checks over the full scalar interval. -/
theorem checked_global_shifted_score {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (d : Transport.ReferenceData) (hlow : d.lowCurveCheck=true) (hgauge : d.gaugeCheck=true)
    (cs : List ReferenceProfileCell) (scalar out : IntegerInterval) (start finish : ℚ)
    (hstart : start≤d.leftContact) (hfinish : d.rightContact≤finish)
    (hcover : coverCheck start finish cs=true)
    (hprofiles : cs.all (fun c => c.check s k)=true)
    (hframes : cs.all (fun c => c.frameCheck d)=true)
    (hshifted : cs.all (fun c => c.shiftedScoreCheck s k scalar out)=true)
    (hlower : (s:ℤ)≤5*out.lo) {S r : ℝ} (hS : scalar.Contains s S)
    (hr : r∈Icc (d.leftContact:ℝ) d.rightContact) :
    1/5≤d.lowScore r+(S-d.slack)*d.globalGaugeDerivative r := by
  have horder := (of_decide_eq_true (Bool.and_eq_true_iff.mp hgauge).1).1
  obtain ⟨c,hmem,hcr⟩ := coverCheck_sound hcover (hstart.trans_lt (horder.trans_le hfinish))
    ⟨(show (start:ℝ)≤d.leftContact by exact_mod_cast hstart).trans hr.1,
      hr.2.trans (by exact_mod_cast hfinish)⟩
  have hframe := List.all_eq_true.mp hframes c hmem
  have hv := frameCheck_values d hlow hgauge c hframe hcr
  have hslack : c.slack=d.slack :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp hframe).1).2.1
  have hh := c.checked_shifted_score hs hk (List.all_eq_true.mp hprofiles c hmem)
    scalar out (List.all_eq_true.mp hshifted c hmem) hS hcr
  rw [hv.1,hv.2.2.2,hslack] at hh
  have hlo : (s:ℝ)≤5*(out.lo:ℝ) := by exact_mod_cast hlower
  have hpos : (0:ℝ)<s := by exact_mod_cast hs
  dsimp [IntegerInterval.Contains] at hh
  nlinarith [hh.1]

end ReferenceProfileCell
end OptimalG.Certificates
