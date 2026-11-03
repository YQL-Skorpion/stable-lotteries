import OptimalG.Certificates.StaticLowHeadSupport
import OptimalG.Certificates.UpperRational
import OptimalG.Certificates.ProfileLookup

/-! Computable rational evaluations of the actual affine-retargeted low profile.
The piece conversion is an exact algebraic identity, not new interpolation data. -/
namespace OptimalG.Certificates.StaticLow
open Set

def scoreQ (r : ℚ) : ℚ :=
  if r≤leftContact then capScoreQ lam slack r else
    if r≤rightContact then scale*UpperTrial.scoreQ r+offset+tilt*(r-leftContact) else lam-r

def primitiveQ (r : ℚ) : ℚ :=
  if r≤leftContact then capQ lam slack r else
    if r≤rightContact then scale*UpperTrial.primitiveQ r+primitiveOffset+
      offset*(r-leftContact)+tilt*(r-leftContact)^2/2 else quadraticQ lam r-slack

def slopeQ (r : ℚ) : ℚ :=
  if r≤rightContact then scale*UpperTrial.slopeQ r+tilt else -1

@[simp] theorem scoreQ_cast (r : ℚ) : (scoreQ r:ℝ)=score r := by
  by_cases hc : r≤leftContact
  · have hc' : (r:ℝ)≤leftContact := by exact_mod_cast hc
    simp [scoreQ,score,hc,hc']
  · have hc' : ¬(r:ℝ)≤leftContact := by exact_mod_cast hc
    by_cases hr : r≤rightContact
    · have hr' : (r:ℝ)≤rightContact := by exact_mod_cast hr
      simp [scoreQ,score,middleScore,centralScore,hc,hc',hr,hr']
    · have hr' : ¬(r:ℝ)≤rightContact := by exact_mod_cast hr
      simp [scoreQ,score,middleScore,hc,hc',hr,hr']

@[simp] theorem primitiveQ_cast (r : ℚ) : (primitiveQ r:ℝ)=primitive r := by
  by_cases hc : r≤leftContact
  · have hc' : (r:ℝ)≤leftContact := by exact_mod_cast hc
    simp [primitiveQ,primitive,hc,hc']
  · have hc' : ¬(r:ℝ)≤leftContact := by exact_mod_cast hc
    by_cases hr : r≤rightContact
    · have hr' : (r:ℝ)≤rightContact := by exact_mod_cast hr
      simp [primitiveQ,primitive,middlePrimitive,centralPrimitive,hc,hc',hr,hr']
    · have hr' : ¬(r:ℝ)≤rightContact := by exact_mod_cast hr
      simp [primitiveQ,primitive,middlePrimitive,hc,hc',hr,hr']

@[simp] theorem slopeQ_cast (r : ℚ) : (slopeQ r:ℝ)=slope r := by
  by_cases hr : r≤rightContact
  · have hr' : (r:ℝ)≤rightContact := by exact_mod_cast hr
    simp [slopeQ,slope,hr,hr']
  · have hr' : ¬(r:ℝ)≤rightContact := by exact_mod_cast hr
    simp [slopeQ,slope,hr,hr']

def retargetPiece (p : CubicPiece) : CubicPiece :=
  ⟨p.lo,p.hi,scale*p.a0+offset+tilt*(p.lo-leftContact),scale*p.a1+tilt,
    scale*p.a2,scale*p.a3,scale*p.f0+primitiveOffset+offset*(p.lo-leftContact)+
      tilt*(p.lo-leftContact)^2/2⟩

theorem retargetPiece_values (p : CubicPiece) (r : ℝ) :
    (retargetPiece p).score (r-p.lo)=(scale:ℝ)*p.score (r-p.lo)+offset+tilt*(r-leftContact) ∧
    (retargetPiece p).primitive (r-p.lo)=(scale:ℝ)*p.primitive (r-p.lo)+primitiveOffset+
      offset*(r-leftContact)+tilt*(r-leftContact)^2/2 ∧
    (retargetPiece p).slope (r-p.lo)=(scale:ℝ)*p.slope (r-p.lo)+tilt := by
  simp only [retargetPiece,CubicPiece.score,CubicPiece.primitive,CubicPiece.slope,
    Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
  constructor
  · ring
  constructor <;> ring

def profilePiece (i : ℕ) : CubicPiece := retargetPiece (Certificates.profilePiece i)

theorem piece_values {i : ℕ} (hi : i<242) {r : ℝ}
    (hr : r∈Ioc ((profilePiece i).lo:ℝ) ((profilePiece i).hi:ℝ)) :
    score r=(profilePiece i).score (r-(profilePiece i).lo) ∧
    primitive r=(profilePiece i).primitive (r-(profilePiece i).lo) ∧
    slope r=(profilePiece i).slope (r-(profilePiece i).lo) := by
  have hc := Certificates.profile_piece_lookup hi
  have hr' : r∈Ioc ((Certificates.profilePiece i).lo:ℝ) (Certificates.profilePiece i).hi := hr
  have hleft : (leftContact:ℝ)≤(Certificates.profilePiece i).lo := by exact_mod_cast hc.2.1
  have hright : ((Certificates.profilePiece i).hi:ℝ)≤rightContact := by exact_mod_cast hc.2.2
  have hb : r∈Icc (leftContact:ℝ) rightContact := ⟨hleft.trans hr'.1.le,hr'.2.trans hright⟩
  obtain ⟨hs,hp,hd⟩ := UpperTrial.piece_values hi hr'
  have hvalues := retargetPiece_values (Certificates.profilePiece i) r
  rw [score_central hb,primitive_central hb,slope,if_pos hb.2]
  dsimp [centralScore,centralPrimitive]
  rw [hs,hp,hd]
  exact ⟨hvalues.1.symm,hvalues.2.1.symm,hvalues.2.2.symm⟩

theorem tail_values {r : ℝ} (hr : (rightContact:ℝ)<r) :
    score r=(lam:ℝ)-r ∧ primitive r=quadratic lam r-slack :=
  ⟨score_line hr.le,primitive_line hr.le⟩

theorem contact_score : score leftContact=((profilePiece 0).a0:ℝ) := by
  rw [score_central ⟨le_rfl,contacts_real.2.2.1.le⟩]
  have hs := UpperTrial.contact_score
  change UpperTrial.score leftContact=(UpperProfileData.piece0.a0:ℝ) at hs
  simp only [centralScore,sub_self,mul_zero,add_zero,hs]
  change _ = ((scale*UpperProfileData.piece0.a0+offset+
    tilt*(UpperProfileData.piece0.lo-leftContact):ℚ):ℝ)
  have hlo : UpperProfileData.piece0.lo=leftContact := UpperProfileData.endpoint_data.1
  simp [hlo]

theorem contact_range : (0.295:ℝ)<leftContact ∧ (leftContact:ℝ)<0.3 := by
  norm_num [leftContact,UpperProfileData.leftContact]

end OptimalG.Certificates.StaticLow
