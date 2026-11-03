import OptimalG.Certificates.StaticLayerGeometry

/-! Semantic values of each admitted supporting cell. -/
namespace OptimalG.Certificates.StaticSupport.ContinuousLayerCell
open RationalPolynomial Set
open StaticLow (lam slack leftContact rightContact)

theorem geometry_parts {c : ContinuousLayerCell} (hc : c.geometryCheck=true) :
    (c.lo<c.hi ∧ c.left.p≤c.lo ∧ c.hi≤c.right.p ∧
      (1/4:ℚ)≤c.left.p ∧ c.right.p≤9/25 ∧ c.left.p<c.right.p ∧
      c.right.p-c.left.p≤3/10000 ∧ c.left.alphau≤3 ∧
      |(c.right.alphau-c.left.alphau)/(c.right.p-c.left.p)|≤2) ∧
    (if c.bIsA then c.lo≤c.a0 ∧ c.hi≤c.a1 else c.a0≤c.lo ∧ c.a1≤c.hi) ∧
    c.primitiveGeometryCheck=true ∧
    (if c.pinned then c.a0=leftContact ∧ c.a1=leftContact ∧ c.aPiece=0 ∧ c.bPiece=0 ∧ c.bIsA=true
      else c.aPiece<242 ∧ profileRangeCheck c.aPiece c.a0 c.a1=true ∧
        profileRangeCheck c.bPiece c.b0 c.b1=true) := by
  cases hp : c.pinned <;> cases hb : c.bIsA <;> simp_all [geometryCheck]
  all_goals aesop

theorem geometry_parameter_bounds {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Icc 0 1) :
    c.pPoly.eval t∈Icc (c.left.p:ℝ) (c.right.p:ℝ) ∧
      c.pPoly.eval t∈Icc (1/4:ℝ) (9/25:ℝ) := by
  have hq := (geometry_parts hc).1
  have hlo : (c.left.p:ℝ)≤c.lo := by exact_mod_cast hq.2.1
  have hhi : (c.hi:ℝ)≤c.right.p := by exact_mod_cast hq.2.2.1
  have hlen : (c.lo:ℝ)<c.hi := by exact_mod_cast hq.1
  have hl : (1/4:ℝ)≤c.left.p := by
    have h : ((1/4:ℚ):ℝ)≤c.left.p := Rat.cast_le.mpr hq.2.2.2.1
    norm_num at h ⊢
    exact h
  have hu : (c.right.p:ℝ)≤9/25 := by
    have h : (c.right.p:ℝ)≤((9/25:ℚ):ℝ) := Rat.cast_le.mpr hq.2.2.2.2.1
    norm_num at h ⊢
    exact h
  have he0 := mul_nonneg (sub_pos.mpr hlen).le ht.1
  have he1 := mul_nonneg (sub_pos.mpr hlen).le (sub_nonneg.mpr ht.2)
  rw [pPoly_eval]
  constructor <;> constructor <;> nlinarith only [hlo,hhi,hl,hu,he0,he1]

theorem geometry_b_max {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Icc 0 1) :
    c.bPoly.eval t=max (c.aPoly.eval t) (c.pPoly.eval t) := by
  have hg := (geometry_parts hc).2.1
  by_cases hb : c.bIsA=true
  · have hq : c.lo≤c.a0 ∧ c.hi≤c.a1 := by simpa only [hb,Bool.true_eq,if_true] using hg
    have h0 : (c.lo:ℝ)≤c.a0 := by exact_mod_cast hq.1
    have h1 : (c.hi:ℝ)≤c.a1 := by exact_mod_cast hq.2
    have hmul0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0)
    have hmul1 := mul_nonneg ht.1 (sub_nonneg.mpr h1)
    have hp : c.pPoly.eval t≤c.aPoly.eval t := by
      rw [pPoly_eval,aPoly_eval]
      nlinarith only [hmul0,hmul1]
    simp only [bPoly,hb,Bool.true_eq,if_true,max_eq_left hp]
  · have hq : c.a0≤c.lo ∧ c.a1≤c.hi := by simpa only [if_neg hb] using hg
    have h0 : (c.a0:ℝ)≤c.lo := by exact_mod_cast hq.1
    have h1 : (c.a1:ℝ)≤c.hi := by exact_mod_cast hq.2
    have hmul0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr h0)
    have hmul1 := mul_nonneg ht.1 (sub_nonneg.mpr h1)
    have hp : c.aPoly.eval t≤c.pPoly.eval t := by
      rw [pPoly_eval,aPoly_eval]
      nlinarith only [hmul0,hmul1]
    simp only [bPoly,if_neg hb,max_eq_right hp]


theorem bPoly_affine (c : ContinuousLayerCell) : c.bPoly=[c.b0,c.b1-c.b0] := by
  cases hb : c.bIsA <;> simp [bPoly,b0,b1,hb,pPoly,aPoly]

theorem geometry_a_lower {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) : (leftContact:ℝ)≤c.aPoly.eval t := by
  have hg := (geometry_parts hc).2.2.2
  by_cases hp : c.pinned=true
  · have h : c.a0=leftContact ∧ c.a1=leftContact ∧ c.aPiece=0 ∧ c.bPiece=0 ∧ c.bIsA=true := by
      simpa only [if_pos hp] using hg
    simp only [aPoly_eval,h.1,h.2.1,sub_self,zero_mul,add_zero,le_refl]
  · have h : c.aPiece<242 ∧ profileRangeCheck c.aPiece c.a0 c.a1=true ∧
        profileRangeCheck c.bPiece c.b0 c.b1=true := by simpa only [if_neg hp] using hg
    have hr := affineRangeCheck_sound (show affineRangeCheck (profilePiece c.aPiece).lo
        (profilePiece c.aPiece).hi c.a0 c.a1=true by
      simpa only [profileRangeCheck,if_pos h.1] using h.2.1) ht
    have hl : (leftContact:ℝ)≤(profilePiece c.aPiece).lo := by
      exact_mod_cast (profile_piece_lookup h.1).2.1
    rw [aPoly_eval]
    linarith [hr.1]

theorem geometry_score_values {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    c.A.eval t=StaticLow.score (c.aPoly.eval t) ∧
      c.B.eval t=StaticLow.score (c.bPoly.eval t) := by
  have hg := (geometry_parts hc).2.2.2
  by_cases hp : c.pinned=true
  · have h : c.a0=leftContact ∧ c.a1=leftContact ∧ c.aPiece=0 ∧ c.bPiece=0 ∧ c.bIsA=true := by
      simpa only [if_pos hp] using hg
    have ha : c.aPoly.eval t=(leftContact:ℝ) := by simp [aPoly_eval,h.1,h.2.1]
    have hb : c.bPoly=c.aPoly := by simp [bPoly,h.2.2.2.2]
    have hpiece : profilePiece 0=piece0 := rfl
    have hfirst : c.A.eval t=StaticLow.score (c.aPoly.eval t) := by
      unfold A
      rw [h.2.2.1,scorePoly_piece_eval (by decide : 0<242),ha,hpiece,piece0_lo,sub_self]
      simpa [CubicPiece.score] using StaticLow.contact_score.symm
    refine ⟨hfirst,?_⟩
    simpa only [B,A,hb,h.2.2.1,h.2.2.2.1] using hfirst
  · have h : c.aPiece<242 ∧ profileRangeCheck c.aPiece c.a0 c.a1=true ∧
        profileRangeCheck c.bPiece c.b0 c.b1=true := by simpa only [if_neg hp] using hg
    constructor
    · rw [A,aPoly_eval]
      exact profileRangeCheck_score h.2.1 ht
    · rw [B,bPoly_eval,bPoly_affine]
      exact profileRangeCheck_score h.2.2 ht

theorem geometry_free_coefficient {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    (hp : c.pinned≠true) {t : ℝ} (ht : t∈Ioo 0 1) :
    c.Cnum.eval t/c.Cden.eval t=-StaticLow.slope (c.aPoly.eval t) := by
  have hg := (geometry_parts hc).2.2.2
  have h : c.aPiece<242 ∧ profileRangeCheck c.aPiece c.a0 c.a1=true ∧
      profileRangeCheck c.bPiece c.b0 c.b1=true := by simpa only [if_neg hp] using hg
  have hs := profileRangeCheck_slope h.1 h.2.1 ht
  simp only [Cnum,Cden,if_neg hp,eval_scale,Rat.cast_neg,Rat.cast_one,RationalPolynomial.eval,
    mul_zero,add_zero,div_one,neg_one_mul]
  rw [aPoly_eval]
  exact congrArg Neg.neg hs

end OptimalG.Certificates.StaticSupport.ContinuousLayerCell
