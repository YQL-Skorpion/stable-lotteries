import OptimalG.Certificates.ReferenceMatchedFields
import OptimalG.VariationalTransferredTransport

/-! The actual Hessian endpoint and the actual support graph give the exact
control disjunction required by logarithmic transport. The early cap branch
uses only the proved cap obstacle; both central cases use exact matching. -/
namespace OptimalG.Certificates.Transport.ReferenceScalarCell
open Set MeasureTheory Variational

theorem matched_coefficient_branch_ae {lam delta M : ℝ} {d : LowRankData}
    {G : ℝ→ℝ} (hd : Admissible lam d) (hdelta : 0≤delta)
    (ref : ReferenceData) (hparam : (ref.lam:ℝ)=lam+delta)
    (hlow : ref.lowCurveCheck=true) (hgauge : ref.gaugeCheck=true)
    (ha : xLo≤ref.leftContact) (hb : (ref.rightContact:ℝ)≤pHi) (hG : Monotone G)
    (hmatch : ∀ r∈Icc (ref.leftContact:ℝ) ref.rightContact,
      G r∈Icc (ref.leftContact:ℝ) ref.rightContact ∧
      ParameterTransfer.shiftedPrimitive lam d delta (G r)=
        ref.transportPrimitive (ParameterTransfer.scalar d.S delta) r)
    (hgood : ∀ᵐ r ∂volume.restrict (Icc (ref.leftContact:ℝ) ref.rightContact),
      0<deriv G r ∧ d.phi (G r)=
        ref.transportScore (ParameterTransfer.scalar d.S delta) r/deriv G r ∧
      (G r,d.phi (G r))∈rankScoreSupport d.phi)
    (c : ReferenceScalarCell) (rb ab : ReferenceProfileBox)
    (hRframe : (c.rProfile rb).frameCheck ref=true)
    (hAframe : (c.aProfile ab).frameCheck ref=true)
    (hlevel : (c.flow.level:ℝ)=M)
    (htime : c.flow.segment.left.z<c.flow.segment.right.z)
    (hR : (c.flow.segment.left.r:ℝ)<c.flow.segment.right.r)
    (hA : (c.flow.segment.left.a:ℝ)<c.flow.segment.right.a)
    (hApiece : c.flow.aPiece.isSome=true)
    (hlate : c.flow.late=true→c.flow.rPiece.isSome=true)
    (hrangeR : c.flow.rPiece.isSome=true →
      Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆
        Icc (ref.leftContact:ℝ) ref.rightContact)
    (hrangeCap : c.flow.rPiece.isSome=false →
      Icc (c.flow.segment.left.r:ℝ) c.flow.segment.right.r ⊆ Icc pLo ref.leftContact)
    (hrangeA : Icc (c.flow.segment.left.a:ℝ) c.flow.segment.right.a ⊆
      Icc (ref.leftContact:ℝ) ref.rightContact)
    (hearly : c.flow.late=false→c.flow.rPiece.isSome=true→
      ∀ s∈Icc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z,
        c.flow.segment.rankMap (·.r) s≤c.flow.segment.rankMap (·.a) s) :
    ∀ᵐ s ∂volume.restrict (Icc (c.flow.segment.left.z:ℝ) c.flow.segment.right.z),
      let S := ParameterTransfer.scalar d.S delta
      let t := c.flow.timeParameter s
      let r := c.globalMatchedRank true G t
      let a' := c.globalMatchedRank false G t
      let R := ref.transportPrimitive S (c.referenceRank true t)
      let mR := ref.transportScore S (c.referenceRank true t)
      let mA := ref.transportScore S (c.referenceRank false t)
      let xiR := c.matchedDerivative true G t
      let xiA := c.matchedDerivative false G t
      let coeff := fun i=>(c.params.coefficients c.flow.late i).eval
        (c.endpointChord t (fun _=>0) S r a')
      (coeff=earlyLogCoefficients (lam+delta) M S
          (highWarp c.start c.finish (S-ref.slack) s) r a' R
          (highWarpSlope c.start c.finish (S-ref.slack)) mA ∧
        ((r,a',a'),mA/xiA,mA/xiA)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r≤R) ∨
      (coeff=lateLogCoefficients (lam+delta) M S
          (highWarp c.start c.finish (S-ref.slack) s) r a' R
          (highWarpSlope c.start c.finish (S-ref.slack)) mR mA ∧
        ((r,a',r),mA/xiA,mR/xiR)∈controlFeatureSupport d ∧
        ParameterTransfer.shiftedPrimitive lam d delta r=R) := by
  have htReal : (c.flow.segment.left.z:ℝ)<c.flow.segment.right.z := by exact_mod_cast htime
  have hsupp := matched_control_support_ae hd hdelta ha hb hG hmatch hgood c
    htReal hR hA hApiece hlate hrangeR hrangeCap hrangeA hearly
  filter_upwards [hsupp,ae_restrict_mem measurableSet_Icc] with s hs hsi
  dsimp only at hs ⊢
  have ht := c.flow.timeParameter_mem htime hsi
  have hp := endpointChord_global_profiles ref hlow hgauge c rb ab hRframe hAframe
    (by exact_mod_cast hR.le) (by exact_mod_cast hA.le) ht
    (ParameterTransfer.scalar d.S delta)
  have hw := c.endpointChord_time (c.flow.timeParameter s) (ParameterTransfer.scalar d.S delta)
  have hmeta := of_decide_eq_true (Bool.and_eq_true_iff.mp hRframe).1
  have hL : c.flow.lam=ref.lam := hmeta.1
  have hS : c.flow.slack=ref.slack := hmeta.2.1
  have hcoeff (i : Fin 4) := c.endpointChord_coefficient (c.flow.timeParameter s) (fun _=>0)
    (ParameterTransfer.scalar d.S delta)
    (c.globalMatchedRank true G (c.flow.timeParameter s))
    (c.globalMatchedRank false G (c.flow.timeParameter s)) i
  simp_rw [hw.1,hw.2,hp.1,hp.2.1,hp.2.2,c.flow.highRank_timeParameter htime s,
    hL,hS,hparam,hlevel] at hcoeff
  cases hl : c.flow.late
  · apply Or.inl
    refine ⟨?_,?_,?_⟩
    · funext i
      simpa only [hl,Bool.false_eq_true,if_false] using hcoeff i
    · simpa only [hl,Bool.false_eq_true,if_false] using hs.1
    · by_cases hrp : c.flow.rPiece.isSome=true
      · have heq := hs.2.1
        rw [if_pos hrp] at heq
        exact heq.le
      · have hrpfalse : c.flow.rPiece.isSome=false := Bool.eq_false_iff.mpr hrp
        have hrbound := hrangeCap hrpfalse (reference_rankMap_bounds c.flow.segment (·.r)
          htReal hR hsi)
        have he := c.referenceRank_timeParameter true s
        have hcap := ref.transportPrimitive_cap (ParameterTransfer.scalar d.S delta)
          (r := c.referenceRank true (c.flow.timeParameter s))
          (by rw [he]; exact hrbound.2)
        rw [hcap,hparam]
        simpa only [hrpfalse,Bool.false_eq_true,if_false] using hs.2.1
  · apply Or.inr
    refine ⟨?_,?_,?_⟩
    · funext i
      simpa only [hl,if_true] using hcoeff i
    · simpa only [hl,if_true] using hs.1
    · simpa only [hlate hl,if_true] using hs.2.1

end OptimalG.Certificates.Transport.ReferenceScalarCell
