import OptimalG.Certificates.StaticLowParameters
import OptimalG.Certificates.CubicIncrements
import OptimalG.Certificates.UpperSupport

/-! An explicit retargeting of the accepted low profile. Continuity, integral
calibration and finite score slopes are inherited by an exact affine change
of the old central score, rather than reconstructed by optimization. -/
namespace OptimalG.Certificates.StaticLow
open Set

@[simp] theorem capQ_cast (L S r : ℚ) : (capQ L S r:ℝ)=cap L S r := by
  simp [capQ,cap]
@[simp] theorem capScoreQ_cast (L S r : ℚ) : (capScoreQ L S r:ℝ)=capSlope L S r := by
  simp [capScoreQ,capSlope]
@[simp] theorem quadraticQ_cast (L r : ℚ) : (quadraticQ L r:ℝ)=quadratic L r := by
  simp [quadraticQ,quadratic]

theorem old_end_values :
    UpperTrial.score rightContact=(UpperProfileData.lam:ℝ)-rightContact ∧
    UpperTrial.primitive rightContact=quadratic UpperProfileData.lam rightContact-
      UpperProfileData.slack := by
  have hpieces : UpperProfileData.pieces.all
      (fun p => decide (p.hi≤rightContact))=true := by decide +kernel
  have ht : Ioi (rightContact:ℝ) ⊆ {r : ℝ |
      UpperTrial.score r=(UpperProfileData.lam:ℝ)-r ∧
      UpperTrial.primitive r=quadratic UpperProfileData.lam r-UpperProfileData.slack} := by
    intro r hr
    have hh := cubic_tail_values (UpperProfileData.lam:ℝ)
      (UpperProfileData.slack:ℝ) r UpperProfileData.pieces (by
        intro p hp
        have hp' : p.hi≤rightContact := of_decide_eq_true (List.all_eq_true.mp hpieces p hp)
        exact (Rat.cast_le.mpr hp').trans_lt hr)
    have hcr : (leftContact:ℝ)<r :=
      (Rat.cast_lt.mpr parameter_bounds.2.2.2.2.1).trans hr
    change UpperTrial.score r=(UpperProfileData.lam:ℝ)-r ∧
      UpperTrial.primitive r=quadratic UpperProfileData.lam r-UpperProfileData.slack
    rw [UpperTrial.score_eq_cubic hcr.le]
    refine ⟨hh.1,?_⟩
    change (if r≤(UpperProfileData.leftContact:ℝ) then _ else _)=_
    have hcr' : (UpperProfileData.leftContact:ℝ)<r := hcr
    rw [if_neg (not_le_of_gt hcr')]
    exact hh.2
  have hc : IsClosed {r : ℝ |
      UpperTrial.score r=(UpperProfileData.lam:ℝ)-r ∧
      UpperTrial.primitive r=quadratic UpperProfileData.lam r-UpperProfileData.slack} :=
    (isClosed_eq UpperTrial.continuous_score (continuous_const.sub continuous_id)).inter
      (isClosed_eq
        (continuous_iff_continuousAt.mpr (fun r => (UpperTrial.primitive_hasDerivAt r).continuousAt))
        (by unfold quadratic; fun_prop))
  have hh := closure_minimal ht hc
  apply hh
  rw [closure_Ioi]
  exact mem_Ici.mpr le_rfl

noncomputable def centralScore (r : ℝ) : ℝ :=
  (scale:ℝ)*UpperTrial.score r+offset+(tilt:ℝ)*(r-leftContact)
noncomputable def centralPrimitive (r : ℝ) : ℝ :=
  (scale:ℝ)*UpperTrial.primitive r+primitiveOffset+
    (offset:ℝ)*(r-leftContact)+(tilt:ℝ)*(r-leftContact)^2/2

theorem centralScore_continuous : Continuous centralScore := by
  unfold centralScore
  exact ((UpperTrial.continuous_score.const_mul _).add continuous_const).add
    (continuous_const.mul (continuous_id.sub continuous_const))

theorem centralPrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt centralPrimitive (centralScore r) r := by
  have hh := (((UpperTrial.primitive_hasDerivAt r).const_mul (scale:ℝ)).add_const
    (primitiveOffset:ℝ)).add (((hasDerivAt_id r).sub_const (leftContact:ℝ)).const_mul (offset:ℝ))
  have ht := (((((hasDerivAt_id r).sub_const (leftContact:ℝ)).pow 2).const_mul
    (tilt:ℝ)).div_const 2)
  convert! hh.add ht using 1 <;> simp [centralPrimitive,centralScore] <;> ring

theorem central_start_values :
    centralScore leftContact=capSlope lam slack leftContact ∧
      centralPrimitive leftContact=cap lam slack leftContact := by
  constructor
  · have hh := congrArg (fun q:ℚ => (q:ℝ)) retarget_endpoints.1
    simpa [centralScore,UpperTrial.score,capCubicScore,leftContact,
      oldStart,newStart,capScoreQ,capSlope] using hh
  · simp [centralPrimitive,UpperTrial.primitive,capCubicPrimitive,leftContact,
      primitiveOffset,capQ,cap]

theorem central_end_values :
    centralScore rightContact=(lam:ℝ)-rightContact ∧
      centralPrimitive rightContact=quadratic lam rightContact-slack := by
  constructor
  · have hh := congrArg (fun q:ℚ => (q:ℝ)) retarget_endpoints.2.1
    rw [centralScore,old_end_values.1]
    simpa [oldEnd,newEnd,width] using hh
  · have hh := congrArg (fun q:ℚ => (q:ℝ)) retarget_endpoints.2.2
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] at hh
    have ho : (oldArea:ℝ)=quadratic UpperProfileData.lam rightContact-
        UpperProfileData.slack-cap UpperProfileData.lam UpperProfileData.slack leftContact := by
      simp [oldArea]
    have hn : (newArea:ℝ)=quadratic lam rightContact-slack-cap lam slack leftContact := by
      simp [newArea]
    have hw : (width:ℝ)=(rightContact:ℝ)-leftContact := by simp [width]
    have hp : (primitiveOffset:ℝ)=cap lam slack leftContact-
        (scale:ℝ)*cap UpperProfileData.lam UpperProfileData.slack leftContact := by
      simp [primitiveOffset]
    rw [ho,hn,hw] at hh
    rw [centralPrimitive,old_end_values.2,hp]
    nlinarith only [hh]

theorem central_increment {r s : ℝ} (hr : (leftContact:ℝ)≤r) (hrs : r≤s) :
    -(s-r)≤centralScore s-centralScore r ∧
      centralScore s-centralScore r≤-(691/1000:ℝ)*(s-r) := by
  have hs := hr.trans hrs
  have hstart : (0.295:ℝ)<leftContact := UpperTrial.contact_range.1
  have h1 := UpperTrial.supporting_line hr
    (show (0.28:ℝ)≤s by linarith only [hstart,hs])
  have h2 := UpperTrial.supporting_line hs
    (show (0.28:ℝ)≤r by linarith only [hstart,hr])
  have hu : UpperProfileData.piece0.slope 0≤-(7/10:ℝ) := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr UpperProfileData.contacts.2.2.2.2
    norm_num [CubicPiece.slope] at hh ⊢
    exact hh.le
  have hupper := mul_le_mul_of_nonneg_right
    ((UpperTrial.slope_bounds hr).2.1.trans hu) (sub_nonneg.mpr hrs)
  have hlower := mul_le_mul_of_nonpos_right (UpperTrial.slope_bounds hs).1
    (sub_nonpos.mpr hrs)
  have hold : -(s-r)≤UpperTrial.score s-UpperTrial.score r ∧
      UpperTrial.score s-UpperTrial.score r≤-(7/10:ℝ)*(s-r) := by
    constructor <;> linarith only [h1,h2,hupper,hlower]
  have hk : (0:ℝ)≤scale := by exact_mod_cast retarget_bounds.1.le
  have hlow := mul_le_mul_of_nonneg_left hold.1 hk
  have hhigh := mul_le_mul_of_nonneg_left hold.2 hk
  have hbl : -(1:ℝ)≤-(scale:ℝ)+tilt := by exact_mod_cast retarget_bounds.2.1
  have hbu : -(7/10:ℝ)*(scale:ℝ)+tilt≤-(691/1000:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr retarget_bounds.2.2
    norm_num only [Rat.cast_add,Rat.cast_mul,Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat] at hh
    exact hh
  have hml := mul_le_mul_of_nonneg_right hbl (sub_nonneg.mpr hrs)
  have hmu := mul_le_mul_of_nonneg_right hbu (sub_nonneg.mpr hrs)
  unfold centralScore
  constructor <;> nlinarith only [hlow,hhigh,hml,hmu]

end OptimalG.Certificates.StaticLow
