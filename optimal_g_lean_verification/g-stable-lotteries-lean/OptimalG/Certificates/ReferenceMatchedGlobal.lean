import OptimalG.Certificates.ReferenceMatching
import OptimalG.Certificates.ReferenceMatchedFrame
import OptimalG.Certificates.ReferenceProfileGlobal

/-! The single global rank matching supplies each finite Hessian cell's
actual primitiveMatch premise. Cap-prefix ranks stay fixed, while central
ranks use the inverse of the same shifted reference primitive. -/
namespace OptimalG.Certificates
open Set
namespace ReferenceProfileCell

theorem frameCheck_central_mem (ref : Transport.ReferenceData) (p : ReferenceProfileCell)
    (hf : p.frameCheck ref=true) (hp : p.piece.isSome=true) {r : ℝ}
    (hr : r∈Icc (p.lo:ℝ) p.hi) : r∈Icc (ref.leftContact:ℝ) ref.rightContact := by
  obtain ⟨hmeta,hgeom⟩ := Bool.and_eq_true_iff.mp hf
  have hm := of_decide_eq_true hmeta
  have htop : p.hi≤ref.rightContact := hm.2.2.2.2.2.2
  cases he : p.piece with
  | none=>simp [he] at hp
  | some piece=>
    have hh : (p.lo≤p.hi ∧ ref.leftContact≤p.lo ∧ piece.lo≤p.lo ∧ p.hi≤piece.hi ∧
        piece.lo<piece.hi) ∧ cubicLookupCheck piece ref.pieces=true := by
      simpa only [Transport.ReferenceFlowCell.localProfileCheck,he,
        Bool.and_eq_true_iff,decide_eq_true_eq] using hgeom
    exact ⟨(show (ref.leftContact:ℝ)≤p.lo by exact_mod_cast hh.1.2.1).trans hr.1,
      hr.2.trans (by exact_mod_cast htop)⟩

end ReferenceProfileCell
namespace Transport.ReferenceScalarCell

noncomputable def globalMatchedRank (c : ReferenceScalarCell) (useR : Bool)
    (G : ℝ→ℝ) (t : ℝ) : ℝ :=
  if (c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩).piece.isSome
  then G (c.referenceRank useR t) else c.referenceRank useR t

theorem globalMatchedRank_late_order (c : ReferenceScalarCell) (G : ℝ→ℝ) (t : ℝ)
    (hG : Monotone G) (hR : c.flow.rPiece.isSome=true) (hA : c.flow.aPiece.isSome=true)
    (horder : c.referenceRank false t≤c.referenceRank true t) :
    c.globalMatchedRank false G t≤c.globalMatchedRank true G t := by
  have hr : c.globalMatchedRank true G t=G (c.referenceRank true t) := by
    simp only [globalMatchedRank,rankProfile,if_true,rProfile,hR,if_true]
  have ha : c.globalMatchedRank false G t=G (c.referenceRank false t) := by
    simp only [globalMatchedRank,rankProfile,Bool.false_eq_true,if_false,aProfile,hA,
      if_true]
  rw [hr,ha]
  exact hG horder

theorem globalMatchedRank_early_central_order (c : ReferenceScalarCell) (G : ℝ→ℝ) (t : ℝ)
    (hG : Monotone G) (hR : c.flow.rPiece.isSome=true) (hA : c.flow.aPiece.isSome=true)
    (horder : c.referenceRank true t≤c.referenceRank false t) :
    c.globalMatchedRank true G t≤c.globalMatchedRank false G t := by
  have hr : c.globalMatchedRank true G t=G (c.referenceRank true t) := by
    simp only [globalMatchedRank,rankProfile,if_true,rProfile,hR,if_true]
  have ha : c.globalMatchedRank false G t=G (c.referenceRank false t) := by
    simp only [globalMatchedRank,rankProfile,Bool.false_eq_true,if_false,aProfile,hA,
      if_true]
  rw [hr,ha]
  exact hG horder

theorem globalMatchedRank_early_order (c : ReferenceScalarCell) (G : ℝ→ℝ) (t cut : ℝ)
    (hR : c.flow.rPiece=none) (hA : c.flow.aPiece.isSome=true)
    (hleft : c.referenceRank true t≤cut) (hmatch : cut≤G (c.referenceRank false t)) :
    c.globalMatchedRank true G t≤c.globalMatchedRank false G t := by
  have hr : c.globalMatchedRank true G t=c.referenceRank true t := by
    simp only [globalMatchedRank,rankProfile,if_true,rProfile,hR,Option.isSome_none,
      Bool.false_eq_true,if_false]
  have ha : c.globalMatchedRank false G t=G (c.referenceRank false t) := by
    simp only [globalMatchedRank,rankProfile,Bool.false_eq_true,if_false,aProfile,hA,
      if_true]
  rw [hr,ha]
  exact hleft.trans hmatch

theorem primitiveMatch_of_global_matching (ref : ReferenceData)
    (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    (c : ReferenceScalarCell) (useR : Bool) (bounds : ReferenceProfileBox)
    (hframe : (c.rankProfile useR bounds).frameCheck ref=true)
    (horder : (c.rankProfile useR bounds).lo≤(c.rankProfile useR bounds).hi)
    {S : ℝ} {J G : ℝ→ℝ}
    (hmatch : ∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
      G r∈Icc (ref.leftContact:ℝ) ref.rightContact ∧ J (G r)=ref.transportPrimitive S r)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    c.primitiveMatch useR S J t (c.globalMatchedRank useR G t) := by
  let p := c.rankProfile useR bounds
  have hr := c.referenceRank_mem useR bounds horder ht
  have hv := ReferenceProfileCell.frameCheck_values ref hlow hgauge p hframe hr
  have hmeta := of_decide_eq_true (Bool.and_eq_true_iff.mp hframe).1
  have hslack : c.flow.slack=ref.slack := by
    cases useR <;> exact hmeta.2.1
  have hleft : c.leftContact=ref.leftContact := by
    cases useR <;> exact hmeta.2.2.1
  have hright : c.rightContact=ref.rightContact := by
    cases useR <;> exact hmeta.2.2.2.1
  have hdef : c.globalMatchedRank useR G t=
      if p.piece.isSome then G (c.referenceRank useR t) else c.referenceRank useR t := by
    cases useR <;> rfl
  rw [hdef]
  have hgoal : c.primitiveMatch useR S J t
      (if p.piece.isSome then G (c.referenceRank useR t) else c.referenceRank useR t) ↔
      (if p.piece.isSome then
        G (c.referenceRank useR t)∈Icc (c.leftContact:ℝ) c.rightContact ∧
        J (G (c.referenceRank useR t))=
          ReferenceFlowCell.localPrimitive p.lam p.slack p.piece (c.referenceRank useR t)+
            (S-c.flow.slack)*p.localGauge (c.referenceRank useR t)
      else True) := by
    cases useR <;> dsimp [primitiveMatch,rankProfile,p,rProfile,aProfile,ReferenceProfileCell.localGauge]
    all_goals split_ifs <;> simp_all
  rw [hgoal]
  by_cases hp : p.piece.isSome=true
  · rw [if_pos hp]
    have hglobal := hmatch _ (ReferenceProfileCell.frameCheck_central_mem ref p hframe hp hr)
    refine ⟨by simpa only [hleft,hright] using hglobal.1,?_⟩
    rw [hglobal.2,ReferenceData.transportPrimitive,hv.2.1,hv.2.2.1,hslack]
  · simp only [if_neg hp]

end Transport.ReferenceScalarCell
end OptimalG.Certificates
