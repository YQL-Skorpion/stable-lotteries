import OptimalG.Certificates.ReferenceProfileCertificate
import OptimalG.Certificates.ReferenceFlowGeometry

/-! A uniform record for the cap and central-polynomial profile checks. Lists
of these records may be checked in bounded batches, with the same real-valued
meaning on both branches. -/
namespace OptimalG.Certificates
open Set

structure ReferenceProfileCell where
  lam : ℚ
  slack : ℚ
  contact : ℚ
  endContact : ℚ
  lo : ℚ
  hi : ℚ
  piece : Option CubicPiece
  gauge : RationalPolynomial
  gaugeDerivative : RationalPolynomial
  bounds : ReferenceProfileBox

namespace ReferenceProfileCell

noncomputable def localGauge (c : ReferenceProfileCell) (r : ℝ) : ℝ :=
  match c.piece with
  | none => -(c.lam:ℝ)/(1-r)
  | some _ => c.gauge.eval ((r-c.contact)/((c.endContact:ℝ)-c.contact))

noncomputable def localGaugeDerivative (c : ReferenceProfileCell) (r : ℝ) : ℝ :=
  match c.piece with
  | none => -(c.lam:ℝ)/(1-r)^2
  | some _ => c.gaugeDerivative.eval ((r-c.contact)/((c.endContact:ℝ)-c.contact))

def check (s k : ℕ) (c : ReferenceProfileCell) : Bool :=
  match c.piece with
  | none => c.bounds.capCheck s c.lam c.slack c.lo c.hi
  | some p => c.bounds.centralCheck s k p c.gauge c.gaugeDerivative
      c.contact c.endContact c.lo c.hi

theorem checked_profiles {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceProfileCell) (hc : c.check s k=true)
    {r : ℝ} (hr : r∈Icc (c.lo:ℝ) c.hi) :
    c.bounds.primitive.Contains s (Transport.ReferenceFlowCell.localPrimitive c.lam c.slack c.piece r) ∧
    c.bounds.score.Contains s (Transport.ReferenceFlowCell.localScore c.lam c.slack c.piece r) ∧
    c.bounds.gauge.Contains s (c.localGauge r) ∧
    c.bounds.gaugeDerivative.Contains s (c.localGaugeDerivative r) := by
  cases hp : c.piece with
  | none =>
    simpa only [check,hp,Transport.ReferenceFlowCell.localPrimitive,
      Transport.ReferenceFlowCell.localScore,localGauge,localGaugeDerivative] using
      c.bounds.capCheck_sound c.lam c.slack c.lo c.hi (by simpa only [check,hp] using hc) hr
  | some p =>
    simpa only [hp,Transport.ReferenceFlowCell.localPrimitive,
      Transport.ReferenceFlowCell.localScore,localGauge,localGaugeDerivative] using
      c.bounds.centralCheck_sound hs hk p c.gauge c.gaugeDerivative c.contact c.endContact
        c.lo c.hi (by simpa only [check,hp] using hc) hr

def shiftedScoreExpr (c : ReferenceProfileCell) : RatExpr 3 :=
  .var 1+(.var 0-.const c.slack)*.var 2

def shiftedScoreBox (c : ReferenceProfileCell) (scalar : IntegerInterval) : Fin 3→IntegerInterval :=
  ![scalar,c.bounds.score,c.bounds.gaugeDerivative]

def shiftedScoreCheck (s k : ℕ) (c : ReferenceProfileCell)
    (scalar out : IntegerInterval) : Bool :=
  c.shiftedScoreExpr.enclosureRefinedCheck s k (c.shiftedScoreBox scalar) out

theorem checked_shifted_score {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceProfileCell) (hc : c.check s k=true)
    (scalar out : IntegerInterval) (hcheck : c.shiftedScoreCheck s k scalar out=true)
    {S r : ℝ} (hS : scalar.Contains s S) (hr : r∈Icc (c.lo:ℝ) c.hi) :
    out.Contains s (Transport.ReferenceFlowCell.localScore c.lam c.slack c.piece r+
      (S-c.slack)*c.localGaugeDerivative r) := by
  have hp := c.checked_profiles hs hk hc hr
  have hx : ∀ i,(c.shiftedScoreBox scalar i).Contains s
      (![S,Transport.ReferenceFlowCell.localScore c.lam c.slack c.piece r,
        c.localGaugeDerivative r] i) := by
    intro i
    fin_cases i
    · simpa [shiftedScoreBox] using hS
    · simpa [shiftedScoreBox] using hp.2.1
    · simpa [shiftedScoreBox] using hp.2.2.2
  have hh := RatExpr.enclosureRefinedCheck_sound hs hk c.shiftedScoreExpr
    (c.shiftedScoreBox scalar) out hcheck _ hx
  simpa [shiftedScoreExpr,RatExpr.eval] using hh

end ReferenceProfileCell
end OptimalG.Certificates
