import OptimalG.Certificates.TransportTerminal
import OptimalG.Certificates.IntegerEnclosures
import OptimalG.Certificates.ExpressionCleanup

/-! The reference budget uses the actual terminal deficit and the actual
auxiliary first-variation endpoint. Its signs follow the logarithmic
reference-minus-terminal comparison. -/
namespace OptimalG.Certificates.Transport
open RatExpr

theorem log_ratio_lower {Z T : ℝ} (hZ : 0<Z) (hT : 0<T) :
    (Z-T)/Z≤Real.log Z-Real.log T := by
  have h := Real.log_le_sub_one_of_pos (div_pos hT hZ)
  rw [Real.log_div hT.ne' hZ.ne'] at h
  have he : (Z-T)/Z=1-T/Z := by rw [sub_div,div_self hZ.ne']
  rw [he]
  linarith

structure ReferenceEndpointCertificate where
  parameters : TerminalParameters
  flowDeficit : IntegerInterval
  flowVariation : IntegerInterval
  terminalDeficit : IntegerInterval
  terminalLogSlope : IntegerInterval
  violation : IntegerInterval
  firstVariation : IntegerInterval

namespace ReferenceEndpointCertificate

def inputBox (c : ReferenceEndpointCertificate) : Fin 4→IntegerInterval :=
  ![c.flowDeficit,c.terminalDeficit,c.flowVariation,c.terminalLogSlope]

def violationExpr : RatExpr 4 := (.var 0-.var 1)/.var 0

def firstVariationExpr : RatExpr 4 := .var 2/.var 0-.var 3

def check (s k : ℕ) (c : ReferenceEndpointCertificate) : Bool :=
  decide (0<c.flowDeficit.lo ∧ 0<c.terminalDeficit.lo) &&
  (c.parameters.deficitExpr.cleanup.enclosureRefinedCheck s k
      (fun _ => IntegerInterval.pointRounded s c.parameters.slack) c.terminalDeficit &&
   (logPartial 0 c.parameters.deficitExpr).cleanup.enclosureRefinedCheck s k
      (fun _ => IntegerInterval.pointRounded s c.parameters.slack) c.terminalLogSlope &&
   violationExpr.enclosureRefinedCheck s k c.inputBox c.violation &&
   firstVariationExpr.enclosureRefinedCheck s k c.inputBox c.firstVariation)

theorem checked_endpoints {s k : ℕ} (hs : 0<s) (hk : 0<k)
    (c : ReferenceEndpointCertificate) (hc : c.check s k=true)
    {Z V : ℝ} (hZ : c.flowDeficit.Contains s Z) (hV : c.flowVariation.Contains s V) :
    0<Z ∧ 0<c.parameters.terminalDeficit c.parameters.slack ∧
    (c.violation.lo:ℝ)/(s:ℝ)≤Real.log Z-Real.log (c.parameters.terminalDeficit c.parameters.slack) ∧
    c.firstVariation.Contains s
      (V/Z-(logPartial 0 c.parameters.deficitExpr).evalOne c.parameters.slack) := by
  obtain ⟨hp,hn⟩ := Bool.and_eq_true_iff.mp hc
  have hp' : 0<c.flowDeficit.lo ∧ 0<c.terminalDeficit.lo := of_decide_eq_true hp
  rcases Bool.and_eq_true_iff.mp hn with ⟨htva,hA⟩
  rcases Bool.and_eq_true_iff.mp htva with ⟨htv,hviol⟩
  rcases Bool.and_eq_true_iff.mp htv with ⟨hT,hD⟩
  have hpoint : ∀ i : Fin 1,(IntegerInterval.pointRounded s c.parameters.slack).Contains s
      (c.parameters.slack:ℝ) := fun _ => IntegerInterval.pointRounded_contains s _
  have hT' := RatExpr.enclosureRefinedCheck_sound hs hk c.parameters.deficitExpr.cleanup
    (fun _ => IntegerInterval.pointRounded s c.parameters.slack) c.terminalDeficit hT
    (fun _ => (c.parameters.slack:ℝ)) hpoint
  have hD' := RatExpr.enclosureRefinedCheck_sound hs hk
    (logPartial 0 c.parameters.deficitExpr).cleanup
    (fun _ => IntegerInterval.pointRounded s c.parameters.slack) c.terminalLogSlope hD
    (fun _ => (c.parameters.slack:ℝ)) hpoint
  rw [RatExpr.cleanup_eval] at hT' hD'
  change c.terminalDeficit.Contains s (c.parameters.deficitExpr.evalOne c.parameters.slack) at hT'
  rw [c.parameters.deficitExpr_eval] at hT'
  have hx : ∀ i,(c.inputBox i).Contains s
      (![Z,c.parameters.terminalDeficit c.parameters.slack,V,
        (logPartial 0 c.parameters.deficitExpr).evalOne c.parameters.slack] i) := by
    intro i
    fin_cases i
    · simpa [inputBox] using hZ
    · simpa [inputBox] using hT'
    · simpa [inputBox] using hV
    · simpa [inputBox,evalOne] using hD'
  have hv := RatExpr.enclosureRefinedCheck_sound hs hk violationExpr c.inputBox c.violation hviol _ hx
  have ha := RatExpr.enclosureRefinedCheck_sound hs hk firstVariationExpr c.inputBox c.firstVariation hA _ hx
  have hzpos := IntegerInterval.positive hs hZ hp'.1
  have htpos := IntegerInterval.positive hs hT' hp'.2
  refine ⟨hzpos,htpos,?_,?_⟩
  · have hv' : c.violation.Contains s ((Z-c.parameters.terminalDeficit c.parameters.slack)/Z) := by
      simpa [violationExpr,eval_divNotation,eval_subNotation,eval] using hv
    exact (IntegerInterval.lower_bound hs hv').trans (log_ratio_lower hzpos htpos)
  · simpa [firstVariationExpr,eval_divNotation,eval_subNotation,eval] using ha

end ReferenceEndpointCertificate
end OptimalG.Certificates.Transport
