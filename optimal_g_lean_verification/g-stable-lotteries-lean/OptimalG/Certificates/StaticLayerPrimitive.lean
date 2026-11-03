import OptimalG.Certificates.StaticLayerValues

/-! Primitive and coefficient identities for the actual continuum layer witness. -/
namespace OptimalG.Certificates.StaticSupport.ContinuousLayerCell
open RationalPolynomial Set
open StaticLow (lam slack leftContact rightContact)

theorem geometry_parameter_local {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Icc 0 1) : c.pPoly.eval t∈Icc (c.lo:ℝ) (c.hi:ℝ) := by
  have hh : (c.lo:ℝ)<c.hi := by exact_mod_cast (geometry_parts hc).1.1
  have hl := mul_nonneg (sub_pos.mpr hh).le ht.1
  have hu := mul_nonneg (sub_pos.mpr hh).le (sub_nonneg.mpr ht.2)
  rw [pPoly_eval]
  constructor <;> nlinarith only [hl,hu]

@[simp] theorem P_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.P.eval t=quadratic lam (1-c.pPoly.eval t)-slack := by
  simp only [P,eval_add,eval_scale,eval_pow,RationalPolynomial.eval,
    Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,quadratic]
  ring

@[simp] theorem k_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.k.eval t=c.pPoly.eval t+c.bPoly.eval t-lam := by
  simp [k,eval_add,RationalPolynomial.eval]
  <;> ring

@[simp] theorem h_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.h.eval t=2*(lam:ℝ)-c.aPoly.eval t := by
  simp [h,eval_add,eval_scale,RationalPolynomial.eval]
  <;> ring

@[simp] theorem nodeWeight_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.nodeWeight.eval t=(c.pPoly.eval t-c.left.p)/((c.right.p:ℝ)-c.left.p) := by
  simp only [nodeWeight,eval_scale,eval_add,RationalPolynomial.eval,Rat.cast_div,
    Rat.cast_sub,Rat.cast_neg,Rat.cast_one,mul_zero,add_zero]
  ring

@[simp] theorem Cu_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.Cu.eval t=(c.left.Cu:ℝ)+((c.right.Cu:ℝ)-c.left.Cu)*
      ((c.pPoly.eval t-c.left.p)/((c.right.p:ℝ)-c.left.p))+1/200000000 := by
  simp only [Cu,eval_add,eval_scale,nodeWeight_eval,RationalPolynomial.eval,
    Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,mul_zero,add_zero]
  ring

@[simp] theorem alphau_eval (c : ContinuousLayerCell) (t : ℝ) :
    c.alphau.eval t=(c.left.alphau:ℝ)+((c.right.alphau:ℝ)-c.left.alphau)*
      ((c.pPoly.eval t-c.left.p)/((c.right.p:ℝ)-c.left.p))+1/200000000 := by
  simp only [alphau,eval_add,eval_scale,nodeWeight_eval,RationalPolynomial.eval,
    Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,mul_zero,add_zero]
  ring

theorem geometry_primitive_value {c : ContinuousLayerCell} (hc : c.geometryCheck=true)
    {t : ℝ} (ht : t∈Ioo 0 1) :
    c.Rnum.eval t/c.Rden.eval t=StaticLow.primitive (c.pPoly.eval t) := by
  have hg := (geometry_parts hc).2.2.1
  cases hb : c.rBranch with
  | cap =>
    have hhi : c.hi≤leftContact := by simpa only [primitiveGeometryCheck,hb,decide_eq_true_eq] using hg
    have hhi' : (c.hi:ℝ)≤leftContact := by exact_mod_cast hhi
    have hr : c.pPoly.eval t≤leftContact := (geometry_parameter_local hc ⟨ht.1.le,ht.2.le⟩).2.trans hhi'
    have hn : 1-c.pPoly.eval t≠0 := by
      have hlt := StaticLow.contact_range.2
      linarith
    rw [StaticLow.primitive_cap hr]
    have hd : c.Rden.eval t=1-c.pPoly.eval t := by
      simp [Rden,hb,eval_add,eval_scale,RationalPolynomial.eval]
      <;> ring
    have hv : c.Rnum.eval t=(1-c.pPoly.eval t)*
        ((lam:ℝ)^2-(lam:ℝ)/2+(lam:ℝ)*c.pPoly.eval t/2)-(lam:ℝ)*slack := by
      simp only [Rnum,hb,eval_add,eval_mul,eval_scale,hd,RationalPolynomial.eval,
        Rat.cast_sub,Rat.cast_neg,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat]
      ring
    rw [hv,hd]
    unfold cap
    field_simp [hn]
    <;> ring
  | piece i =>
    have h : i<242 ∧ profileRangeCheck i c.lo c.hi=true := by
      simpa only [primitiveGeometryCheck,hb,Bool.and_eq_true,decide_eq_true_eq] using hg
    have hr := affineRangeCheck_sound (show affineRangeCheck (profilePiece i).lo
        (profilePiece i).hi c.lo c.hi=true by
      simpa only [profileRangeCheck,if_pos h.1] using h.2) ht
    have hp := (StaticLow.piece_values h.1 hr).2.1
    rw [pPoly_eval]
    rw [hp]
    simp only [Rnum,Rden,hb,eval_compose,eval_add,RationalPolynomial.eval,
      Rat.cast_neg,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one,CubicPiece.primitive,pPoly_eval]
    ring
  | tail =>
    have h : affineRangeCheck rightContact (max c.lo c.hi) c.lo c.hi=true := by
      simpa only [primitiveGeometryCheck,hb] using hg
    have hr := affineRangeCheck_sound h ht
    have hp := (StaticLow.tail_values hr.1).2
    rw [pPoly_eval,hp]
    simp only [Rnum,Rden,hb,eval_add,eval_scale,eval_pow,RationalPolynomial.eval,
      Rat.cast_neg,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,quadratic,pPoly_eval]
    ring

end OptimalG.Certificates.StaticSupport.ContinuousLayerCell
