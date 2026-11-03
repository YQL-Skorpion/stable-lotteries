import OptimalG.Certificates.TransportReference
import OptimalG.Certificates.CapCubic

/-! The reference scalar gauge is genuinely C¹ across its cap, polynomial,
and constant pieces. Both endpoint values and derivatives come from the
exact rational gauge check. -/
namespace OptimalG.Certificates.Transport.ReferenceData
open Set

noncomputable def globalGauge (d : ReferenceData) (r : ℝ) : ℝ :=
  if r≤d.leftContact then -(d.lam:ℝ)/(1-r)
  else if r≤d.rightContact then d.centralGauge r else -1

noncomputable def globalGaugeDerivative (d : ReferenceData) (r : ℝ) : ℝ :=
  if r≤d.leftContact then -(d.lam:ℝ)/(1-r)^2
  else if r≤d.rightContact then d.centralGaugeDerivative r else 0

theorem globalGauge_hasDerivAt {d : ReferenceData} (hc : d.gaugeCheck=true) (r : ℝ) :
    HasDerivAt d.globalGauge (d.globalGaugeDerivative r) r := by
  have hr := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hab : (d.leftContact:ℝ)<d.rightContact := by exact_mod_cast hr.1
  have ha1 : (d.leftContact:ℝ)<1 := by exact_mod_cast hr.2.1
  have he := gauge_endpoints hc
  have htail (x : ℝ) := hasDerivAt_glue_le (d.rightContact:ℝ)
    d.centralGauge (fun _ => -1) d.centralGaugeDerivative (fun _ => 0)
    (gauge_derivative hc) (fun x => hasDerivAt_const x (-1:ℝ)) he.2.1 he.2.2.2 x
  apply hasDerivAt_glue_le_of_left (d.leftContact:ℝ)
    (fun x => -(d.lam:ℝ)/(1-x))
    (fun x => if x≤d.rightContact then d.centralGauge x else -1)
    (fun x => -(d.lam:ℝ)/(1-x)^2)
    (fun x => if x≤d.rightContact then d.centralGaugeDerivative x else 0)
    ?_ htail ?_ ?_ r
  · intro x hx
    have hh := (hasDerivAt_const x (-(d.lam:ℝ))).div
      ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
      (ne_of_gt (sub_pos.mpr (hx.trans_lt ha1)))
    convert! hh using 1 <;> simp <;> ring
  · simpa only [if_pos hab.le] using he.1.symm
  · simpa only [if_pos hab.le] using he.2.2.1.symm

theorem globalGauge_continuous {d : ReferenceData} (hc : d.gaugeCheck=true) :
    Continuous d.globalGauge := continuous_iff_continuousAt.mpr
  (fun r => (globalGauge_hasDerivAt hc r).continuousAt)

theorem globalGaugeDerivative_continuous {d : ReferenceData} (hc : d.gaugeCheck=true) :
    Continuous d.globalGaugeDerivative := by
  have hr := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hab : (d.leftContact:ℝ)<d.rightContact := by exact_mod_cast hr.1
  have ha1 : (d.leftContact:ℝ)<1 := by exact_mod_cast hr.2.1
  have he := gauge_endpoints hc
  have hcentral : Continuous d.centralGaugeDerivative :=
    d.gaugeDerivative.continuous_eval.comp (by fun_prop)
  have htail : Continuous (fun r : ℝ => if r≤d.rightContact then d.centralGaugeDerivative r else 0) :=
    hcentral.if_le continuous_const continuous_id continuous_const (fun r h => by
      change r=(d.rightContact:ℝ) at h
      subst r
      exact he.2.2.2)
  have hmin : Continuous (fun r : ℝ => min r d.leftContact) := continuous_id.min continuous_const
  have hleft : Continuous (fun r : ℝ => -(d.lam:ℝ)/(1-min r d.leftContact)^2) :=
    continuous_const.div ((continuous_const.sub hmin).pow 2) (fun r =>
      pow_ne_zero _ (ne_of_gt (sub_pos.mpr ((min_le_right _ _).trans_lt ha1))))
  have hh := hleft.if_le htail continuous_id continuous_const (fun r h => by
    change r=(d.leftContact:ℝ) at h
    subst r
    simpa only [min_self,if_pos hab.le] using he.2.2.1.symm)
  convert! hh using 1
  funext r
  by_cases hrc : r≤d.leftContact
  · simp only [globalGaugeDerivative,id_eq,if_pos hrc,min_eq_left hrc]
  · simp only [globalGaugeDerivative,id_eq,if_neg hrc]

theorem globalGauge_cap {d : ReferenceData} {r : ℝ} (hr : r≤d.leftContact) :
    d.globalGauge r= -(d.lam:ℝ)/(1-r) := if_pos hr

theorem globalGauge_central {d : ReferenceData} (hc : d.gaugeCheck=true)
    {r : ℝ} (hr : r∈Icc (d.leftContact:ℝ) d.rightContact) :
    d.globalGauge r=d.centralGauge r := by
  by_cases hrc : r≤d.leftContact
  · have he : r=(d.leftContact:ℝ) := le_antisymm hrc hr.1
    subst r
    simpa only [globalGauge,if_pos le_rfl] using (gauge_endpoints hc).1.symm
  · simp only [globalGauge,if_neg hrc,if_pos hr.2]

theorem globalGauge_tail {d : ReferenceData} (hc : d.gaugeCheck=true)
    {r : ℝ} (hr : (d.rightContact:ℝ)≤r) : d.globalGauge r= -1 := by
  have hg := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hab : (d.leftContact:ℝ)<d.rightContact := by exact_mod_cast hg.1
  rw [globalGauge,if_neg (not_le_of_gt (hab.trans_le hr))]
  by_cases hrc : r≤d.rightContact
  · have he : r=(d.rightContact:ℝ) := le_antisymm hrc hr
    subst r
    simpa only [if_pos le_rfl] using (gauge_endpoints hc).2.1
  · exact if_neg hrc

theorem globalGaugeDerivative_cap {d : ReferenceData} {r : ℝ} (hr : r≤d.leftContact) :
    d.globalGaugeDerivative r= -(d.lam:ℝ)/(1-r)^2 := if_pos hr

theorem globalGaugeDerivative_central {d : ReferenceData} (hc : d.gaugeCheck=true)
    {r : ℝ} (hr : r∈Icc (d.leftContact:ℝ) d.rightContact) :
    d.globalGaugeDerivative r=d.centralGaugeDerivative r := by
  by_cases hrc : r≤d.leftContact
  · have he : r=(d.leftContact:ℝ) := le_antisymm hrc hr.1
    subst r
    simpa only [globalGaugeDerivative,if_pos le_rfl] using (gauge_endpoints hc).2.2.1.symm
  · simp only [globalGaugeDerivative,if_neg hrc,if_pos hr.2]

theorem globalGaugeDerivative_tail {d : ReferenceData} (hc : d.gaugeCheck=true)
    {r : ℝ} (hr : (d.rightContact:ℝ)≤r) : d.globalGaugeDerivative r=0 := by
  have hg := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
  have hab : (d.leftContact:ℝ)<d.rightContact := by exact_mod_cast hg.1
  rw [globalGaugeDerivative,if_neg (not_le_of_gt (hab.trans_le hr))]
  by_cases hrc : r≤d.rightContact
  · have he : r=(d.rightContact:ℝ) := le_antisymm hrc hr
    subst r
    simpa only [if_pos le_rfl] using (gauge_endpoints hc).2.2.2
  · exact if_neg hrc

theorem warpedReference_hasDerivAt {d : ReferenceData} (hc : d.gaugeCheck=true)
    {F : ℝ → ℝ} {f S r : ℝ} (hF : HasDerivAt F f r) :
    HasDerivAt (fun x => F x+(S-d.slack)*d.globalGauge x)
      (f+(S-d.slack)*d.globalGaugeDerivative r) r :=
  hF.add ((globalGauge_hasDerivAt hc r).const_mul (S-d.slack))

theorem warpedReference_cap {d : ReferenceData} {F : ℝ → ℝ} {S r : ℝ}
    (hr : r≤d.leftContact) (hF : F r=cap d.lam d.slack r) :
    F r+(S-d.slack)*d.globalGauge r=cap d.lam S r := by
  rw [hF,globalGauge_cap hr]
  unfold cap
  ring

theorem warpedReference_tail {d : ReferenceData} (hc : d.gaugeCheck=true)
    {F : ℝ → ℝ} {S r : ℝ} (hr : (d.rightContact:ℝ)≤r)
    (hF : F r=quadratic d.lam r-d.slack) :
    F r+(S-d.slack)*d.globalGauge r=quadratic d.lam r-S := by
  rw [hF,globalGauge_tail hc hr]
  ring

end OptimalG.Certificates.Transport.ReferenceData
