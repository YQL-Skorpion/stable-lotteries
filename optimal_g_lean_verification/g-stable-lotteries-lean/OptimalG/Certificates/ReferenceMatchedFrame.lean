import OptimalG.Certificates.ReferenceRankMatch
import OptimalG.Certificates.ReferenceRankCompact
import OptimalG.Certificates.ReferenceFrozenProfiles

/-! A matched rank is either the unchanged cap-prefix reference rank or
the genuine inverse of the shifted reference primitive. This is the exact
endpoint data used when certifying a comparison chord. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set

def rankProfile (c : ReferenceScalarCell) (useR : Bool) (bounds : ReferenceProfileBox) :
    ReferenceProfileCell := if useR then c.rProfile bounds else c.aProfile bounds

noncomputable def referenceRank (c : ReferenceScalarCell) (useR : Bool) (t : ℝ) : ℝ :=
  if useR then c.flow.rankR.evalOne t else c.flow.rankA.evalOne t

def profileMatch (c : ReferenceScalarCell) (useR : Bool) (d : Variational.LowRankData)
    (t r : ℝ) : Prop :=
  let profile := c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩
  if profile.piece.isSome then
    r∈Icc (c.leftContact:ℝ) c.rightContact ∧
      Variational.lowPrimitive c.flow.lam d r=
        ReferenceFlowCell.localPrimitive profile.lam profile.slack profile.piece
          (c.referenceRank useR t)+
          (d.S-c.flow.slack)*profile.localGauge (c.referenceRank useR t)
  else r=c.referenceRank useR t

def primitiveMatch (c : ReferenceScalarCell) (useR : Bool) (S : ℝ) (J : ℝ→ℝ)
    (t r : ℝ) : Prop :=
  let profile := c.rankProfile useR ⟨⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩⟩
  if profile.piece.isSome then
    r∈Icc (c.leftContact:ℝ) c.rightContact ∧
      J r=ReferenceFlowCell.localPrimitive profile.lam profile.slack profile.piece
          (c.referenceRank useR t)+
        (S-c.flow.slack)*profile.localGauge (c.referenceRank useR t)
  else r=c.referenceRank useR t

def rankLinkCheck (c : ReferenceScalarCell) (useR : Bool) (bounds : ReferenceProfileBox)
    (rank : ReferenceRankCell) (scalar : IntegerInterval) : Bool :=
  let profile := c.rankProfile useR bounds
  decide (rank.tube.lam=c.flow.lam ∧ rank.tube.referenceSlack=c.flow.slack ∧
    rank.tube.leftContact=c.leftContact ∧ rank.tube.rightContact=c.rightContact ∧
    rank.matched=profile.piece.isSome ∧ rank.referenceLo=profile.lo ∧
    rank.referenceHi=profile.hi ∧ rank.tube.input=![scalar,bounds.primitive,bounds.gauge])

theorem referenceRank_mem (c : ReferenceScalarCell) (useR : Bool)
    (bounds : ReferenceProfileBox)
    (ho : (c.rankProfile useR bounds).lo≤(c.rankProfile useR bounds).hi)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    c.referenceRank useR t∈Icc ((c.rankProfile useR bounds).lo:ℝ)
      (c.rankProfile useR bounds).hi := by
  cases useR <;>
    exact ReferenceFlowCell.affineExpr_mem ho ht

theorem checked_matched_rank {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (useR : Bool) (bounds : ReferenceProfileBox)
    (rank : ReferenceRankCell) (scalar : IntegerInterval)
    (hp : (c.rankProfile useR bounds).check s k=true)
    (hrank : rank.check s k=true) (hlink : c.rankLinkCheck useR bounds rank scalar=true)
    (horder : (c.rankProfile useR bounds).lo≤(c.rankProfile useR bounds).hi)
    {d : Variational.LowRankData} (hd : Variational.Admissible c.flow.lam d)
    (hleft : Variational.ell≤(c.leftContact:ℝ))
    (hright : (c.rightContact:ℝ)≤Variational.tEnd)
    (hS : scalar.Contains s d.S) {t r : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hm : c.profileMatch useR d t r) : rank.bounds.Contains s r := by
  let p := c.rankProfile useR bounds
  have hvals := p.checked_profiles hs hk hp (c.referenceRank_mem useR bounds horder ht)
  have hl : rank.tube.lam=c.flow.lam ∧ rank.tube.referenceSlack=c.flow.slack ∧
      rank.tube.leftContact=c.leftContact ∧ rank.tube.rightContact=c.rightContact ∧
      rank.matched=p.piece.isSome ∧ rank.referenceLo=p.lo ∧ rank.referenceHi=p.hi ∧
      rank.tube.input=![scalar,bounds.primitive,bounds.gauge] := of_decide_eq_true hlink
  have hbounds : p.bounds=bounds := by cases useR <;> rfl
  rw [hbounds] at hvals
  apply rank.checked_contains_of_match hs hk hrank (by simpa only [hl.1] using hd)
    (by simpa only [hl.2.2.1] using hleft) (by simpa only [hl.2.2.2.1] using hright)
    (F:=ReferenceFlowCell.localPrimitive p.lam p.slack p.piece (c.referenceRank useR t))
    (u:=p.localGauge (c.referenceRank useR t))
  · rw [hl.2.2.2.2.2.2.2]
    intro i
    fin_cases i
    · exact hS
    · exact hvals.1
    · exact hvals.2.2.1
  · rw [hl.2.2.2.2.1,hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1,
      hl.2.2.2.2.2.1,hl.2.2.2.2.2.2.1]
    have hm' : if p.piece.isSome then
        r∈Icc (c.leftContact:ℝ) c.rightContact ∧
          Variational.lowPrimitive c.flow.lam d r=
            ReferenceFlowCell.localPrimitive p.lam p.slack p.piece (c.referenceRank useR t)+
              (d.S-c.flow.slack)*p.localGauge (c.referenceRank useR t)
        else r=c.referenceRank useR t := by
      cases useR <;> exact hm
    split_ifs at hm' ⊢ with h
    · exact hm'
    · rw [hm']
      exact c.referenceRank_mem useR bounds horder ht

theorem checked_primitive_matched_rank {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceScalarCell) (useR : Bool) (bounds : ReferenceProfileBox)
    (rank : ReferenceRankCell) (scalar : IntegerInterval)
    (hp : (c.rankProfile useR bounds).check s k=true)
    (hrank : rank.check s k=true) (hlink : c.rankLinkCheck useR bounds rank scalar=true)
    (horder : (c.rankProfile useR bounds).lo≤(c.rankProfile useR bounds).hi)
    {S : ℝ} {J : ℝ→ℝ} (hL : Compact.LambdaRange c.flow.lam) (hSl : S≤(3:ℝ)/100)
    (hleft : Variational.ell≤(c.leftContact:ℝ))
    (hright : (c.rightContact:ℝ)≤Variational.tEnd)
    (hobstacle : ∀ r∈Icc (c.leftContact:ℝ) c.rightContact,
      quadratic c.flow.lam r-S≤J r ∧ J r≤cap c.flow.lam S r)
    (hS : scalar.Contains s S) {t r : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hm : c.primitiveMatch useR S J t r) : rank.bounds.Contains s r := by
  let p := c.rankProfile useR bounds
  have hvals := p.checked_profiles hs hk hp (c.referenceRank_mem useR bounds horder ht)
  have hl : rank.tube.lam=c.flow.lam ∧ rank.tube.referenceSlack=c.flow.slack ∧
      rank.tube.leftContact=c.leftContact ∧ rank.tube.rightContact=c.rightContact ∧
      rank.matched=p.piece.isSome ∧ rank.referenceLo=p.lo ∧ rank.referenceHi=p.hi ∧
      rank.tube.input=![scalar,bounds.primitive,bounds.gauge] := of_decide_eq_true hlink
  have hbounds : p.bounds=bounds := by cases useR <;> rfl
  rw [hbounds] at hvals
  apply rank.checked_contains_compact hs hk hrank (by simpa only [hl.1] using hL) hSl
    (by simpa only [hl.2.2.1] using hleft) (by simpa only [hl.2.2.2.1] using hright)
    (F:=ReferenceFlowCell.localPrimitive p.lam p.slack p.piece (c.referenceRank useR t))
    (u:=p.localGauge (c.referenceRank useR t))
  · rw [hl.2.2.2.2.2.2.2]
    intro i
    fin_cases i
    · exact hS
    · exact hvals.1
    · exact hvals.2.2.1
  · rw [hl.2.2.2.2.1,hl.1,hl.2.1,hl.2.2.1,hl.2.2.2.1,
      hl.2.2.2.2.2.1,hl.2.2.2.2.2.2.1]
    have hm' : if p.piece.isSome then
        r∈Icc (c.leftContact:ℝ) c.rightContact ∧
          J r=ReferenceFlowCell.localPrimitive p.lam p.slack p.piece (c.referenceRank useR t)+
            (S-c.flow.slack)*p.localGauge (c.referenceRank useR t)
        else r=c.referenceRank useR t := by
      cases useR <;> exact hm
    split_ifs at hm' ⊢ with h
    · have ho := hobstacle r hm'.1
      rw [hm'.2] at ho
      exact ⟨hm'.1,ho.2,ho.1⟩
    · rw [hm']
      exact c.referenceRank_mem useR bounds horder ht

end OptimalG.Certificates.Transport.ReferenceScalarCell
