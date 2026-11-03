import OptimalG.Certificates.ReferenceFlowExpressions
import OptimalG.Certificates.CubicLookup

/-! Local cap/cubic expressions in a flow certificate are checked against the
single assembled low reference, including the shared contact endpoint. -/
namespace OptimalG.Certificates.Transport.ReferenceFlowCell
open Set

def localProfileCheck (contact : ℚ) (pieces : List CubicPiece)
    (p : Option CubicPiece) (lo hi : ℚ) : Bool :=
  match p with
  | none => decide (lo≤hi ∧ hi≤contact)
  | some p => decide (lo≤hi ∧ contact≤lo ∧ p.lo≤lo ∧ hi≤p.hi ∧ p.lo<p.hi) &&
      cubicLookupCheck p pieces

theorem localProfileCheck_values {L S contact lo hi : ℚ} {pieces : List CubicPiece}
    {p : Option CubicPiece} (hc : localProfileCheck contact pieces p lo hi=true)
    (hscore : Continuous (cubicScore L pieces))
    (hprimitive : Continuous (cubicPrimitive L S pieces))
    (hjoin : cap L S contact=cubicPrimitive L S pieces contact ∧
      capSlope L S contact=cubicScore L pieces contact)
    {r : ℝ} (hr : r∈Icc (lo:ℝ) hi) :
    localScore L S p r=capCubicScore L S contact pieces r ∧
      localPrimitive L S p r=capCubicPrimitive L S contact pieces r := by
  cases p with
  | none =>
    have hh : lo≤hi ∧ hi≤contact := of_decide_eq_true hc
    have hrc : r≤(contact:ℝ) := hr.2.trans (by exact_mod_cast hh.2)
    simp only [localScore,localPrimitive,capCubicScore,capCubicPrimitive,if_pos hrc]
    trivial
  | some p =>
    have hh : (lo≤hi ∧ contact≤lo ∧ p.lo≤lo ∧ hi≤p.hi ∧ p.lo<p.hi) ∧
        cubicLookupCheck p pieces=true := by
      simpa only [localProfileCheck,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    have hp : r∈Icc (p.lo:ℝ) p.hi :=
      ⟨(show (p.lo:ℝ)≤lo by exact_mod_cast hh.1.2.2.1).trans hr.1,
        hr.2.trans (by exact_mod_cast hh.1.2.2.2.1)⟩
    have he := cubicLookupCheck_closed_values hh.2 hh.1.2.2.2.2 L S hscore hprimitive hp
    by_cases hrc : r≤(contact:ℝ)
    · have hcr : (contact:ℝ)≤r := (show (contact:ℝ)≤lo by exact_mod_cast hh.1.2.1).trans hr.1
      have her : r=(contact:ℝ) := le_antisymm hrc hcr
      subst r
      simpa only [localScore,localPrimitive,capCubicScore,capCubicPrimitive,if_pos le_rfl]
        using And.intro (he.1.symm.trans hjoin.2.symm) (he.2.symm.trans hjoin.1.symm)
    · simpa only [localScore,localPrimitive,capCubicScore,capCubicPrimitive,if_neg hrc]
        using And.intro he.1.symm he.2.symm

theorem affineExpr_mem {lo hi : ℚ} (h : lo≤hi) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (affineExpr lo hi).evalOne t∈Icc (lo:ℝ) hi := by
  have h' : (lo:ℝ)≤hi := by exact_mod_cast h
  simp only [affineExpr,RatExpr.evalOne,RatExpr.eval_addNotation,RatExpr.eval_mulNotation,
    RatExpr.eval,Rat.cast_sub]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr h') ht.1,
    mul_nonneg (sub_nonneg.mpr h') (show 0≤1-t by linarith [ht.2])]

def geometryCheck (contact : ℚ) (pieces : List CubicPiece) (c : ReferenceFlowCell) : Bool :=
  localProfileCheck contact pieces c.rPiece c.segment.left.r c.segment.right.r &&
    (localProfileCheck contact pieces c.aPiece c.segment.left.a c.segment.right.a &&
      decide (c.segment.left.z<c.segment.right.z))

theorem geometryCheck_profiles {contact : ℚ} {pieces : List CubicPiece} {c : ReferenceFlowCell}
    (hc : c.geometryCheck contact pieces=true)
    (hscore : Continuous (cubicScore c.lam pieces))
    (hprimitive : Continuous (cubicPrimitive c.lam c.slack pieces))
    (hjoin : cap c.lam c.slack contact=cubicPrimitive c.lam c.slack pieces contact ∧
      capSlope c.lam c.slack contact=cubicScore c.lam pieces contact)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (localScore c.lam c.slack c.rPiece (c.rankR.evalOne t)=
      capCubicScore c.lam c.slack contact pieces (c.rankR.evalOne t) ∧
     localPrimitive c.lam c.slack c.rPiece (c.rankR.evalOne t)=
      capCubicPrimitive c.lam c.slack contact pieces (c.rankR.evalOne t)) ∧
    (localScore c.lam c.slack c.aPiece (c.rankA.evalOne t)=
      capCubicScore c.lam c.slack contact pieces (c.rankA.evalOne t) ∧
     localPrimitive c.lam c.slack c.aPiece (c.rankA.evalOne t)=
      capCubicPrimitive c.lam c.slack contact pieces (c.rankA.evalOne t)) := by
  have hh := Bool.and_eq_true_iff.mp hc
  have hr : c.segment.left.r≤c.segment.right.r := by
    cases hp : c.rPiece <;>
      simp only [localProfileCheck,hp,Bool.and_eq_true_iff,decide_eq_true_eq] at hh <;> tauto
  have ha : c.segment.left.a≤c.segment.right.a := by
    have h := (Bool.and_eq_true_iff.mp hh.2).1
    cases hp : c.aPiece <;>
      simp only [localProfileCheck,hp,Bool.and_eq_true_iff,decide_eq_true_eq] at h <;> tauto
  exact ⟨localProfileCheck_values hh.1 hscore hprimitive hjoin (affineExpr_mem hr ht),
    localProfileCheck_values (Bool.and_eq_true_iff.mp hh.2).1 hscore hprimitive hjoin (affineExpr_mem ha ht)⟩

end OptimalG.Certificates.Transport.ReferenceFlowCell
