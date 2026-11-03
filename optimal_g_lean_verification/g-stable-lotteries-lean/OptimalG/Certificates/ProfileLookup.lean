import OptimalG.Certificates.ProfileLookupData
import OptimalG.Certificates.UpperSupport

/-! The polynomial branches used by continuous certificates evaluate to the
actual corrected trial, including its cap prefix and final quadratic tail. -/
namespace OptimalG.Certificates
open Set UpperProfileData

namespace UpperTrial

theorem piece_values {i : ℕ} (hi : i<242) {r : ℝ}
    (hr : r∈Ioc ((profilePiece i).lo:ℝ) ((profilePiece i).hi:ℝ)) :
    score r=(profilePiece i).score (r-(profilePiece i).lo) ∧
      primitive r=(profilePiece i).primitive (r-(profilePiece i).lo) ∧
      slope r=(profilePiece i).slope (r-(profilePiece i).lo) := by
  have hc := profile_piece_lookup hi
  have hl : (leftContact:ℝ)≤(profilePiece i).lo := by exact_mod_cast hc.2.1
  have hn : ¬r≤leftContact := by linarith [hr.1]
  have hv := cubicLookupCheck_values hc.1 (lam:ℝ) (slack:ℝ) hr
  simpa only [score,primitive,slope,capCubicScore,capCubicPrimitive,if_neg hn] using hv

theorem tail_values {r : ℝ} (hr : (rightContact:ℝ)<r) :
    score r=(lam:ℝ)-r ∧ primitive r=quadratic lam r-slack := by
  have hh : (leftContact:ℝ)<rightContact := by
    have hc := contacts
    norm_num at hc ⊢
    exact_mod_cast (show leftContact<rightContact by linarith only [hc.2.1,hc.2.2.1])
  have hn : ¬r≤leftContact := by linarith
  have he : ∀ p∈pieces, (p.hi:ℝ)<r := by
    intro p hp
    have h : p.hi≤rightContact := of_decide_eq_true (List.all_eq_true.mp all_hi_le_right p hp)
    have h' : (p.hi:ℝ)≤rightContact := by exact_mod_cast h
    linarith
  have hv := cubic_tail_values (lam:ℝ) (slack:ℝ) r pieces he
  simpa only [score,primitive,capCubicScore,capCubicPrimitive,if_neg hn,quadratic] using hv

theorem cap_primitive {r : ℝ} (hr : r≤leftContact) : primitive r=cap lam slack r := by
  exact if_pos hr

theorem contact_score : score leftContact=(piece0.a0:ℝ) := by
  change capCubicScore lam slack leftContact pieces leftContact=_
  rw [capCubicScore,if_pos le_rfl]
  have h := congrArg (fun q:ℚ => (q:ℝ)) endpoint_data.2.2.1
  simpa [capSlope] using h.symm

end UpperTrial

/-- Closed endpoint data give strict left membership at every interior convex
combination, provided the two endpoint values are not both at the left edge. -/
def affineRangeCheck (lo hi a b : ℚ) : Bool :=
  decide (lo≤a ∧ lo≤b ∧ a≤hi ∧ b≤hi ∧ (lo<a ∨ lo<b))

theorem affineRangeCheck_sound {lo hi a b : ℚ} (hc : affineRangeCheck lo hi a b=true)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    (a:ℝ)+((b:ℝ)-a)*t∈Ioc (lo:ℝ) (hi:ℝ) := by
  have hq : lo≤a ∧ lo≤b ∧ a≤hi ∧ b≤hi ∧ (lo<a ∨ lo<b) := of_decide_eq_true hc
  have ha : (lo:ℝ)≤a := by exact_mod_cast hq.1
  have hb : (lo:ℝ)≤b := by exact_mod_cast hq.2.1
  have hau : (a:ℝ)≤hi := by exact_mod_cast hq.2.2.1
  have hbu : (b:ℝ)≤hi := by exact_mod_cast hq.2.2.2.1
  have ht0 : 0≤t := ht.1.le
  have ht1 : 0≤1-t := (sub_pos.mpr ht.2).le
  constructor
  · rcases hq.2.2.2.2 with ha' | hb'
    · have ha'' : (lo:ℝ)<a := by exact_mod_cast ha'
      have h1 := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr ha'')
      have h2 := mul_nonneg ht0 (sub_nonneg.mpr hb)
      nlinarith only [h1,h2]
    · have hb'' : (lo:ℝ)<b := by exact_mod_cast hb'
      have h1 := mul_nonneg ht1 (sub_nonneg.mpr ha)
      have h2 := mul_pos ht.1 (sub_pos.mpr hb'')
      nlinarith only [h1,h2]
  · have h1 := mul_nonneg ht1 (sub_nonneg.mpr hau)
    have h2 := mul_nonneg ht0 (sub_nonneg.mpr hbu)
    nlinarith only [h1,h2]

end OptimalG.Certificates
