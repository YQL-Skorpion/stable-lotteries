import OptimalG.VariationalTransportSource
import OptimalG.VariationalLinearCoercivity

/-! Assembly of the logarithmic flow and terminal Taylor inequalities.
The reference terminal mismatch retains its sign; neither the initial
logarithmic deficit nor the final matching displacement is discarded. -/
namespace OptimalG.Variational
open Set MeasureTheory

theorem transport_flow_terminal_combine
    {initial flow position derivative entropy Aflow Aterminal ds
      flowCurvature terminalCurvature rankLoss variation
      w wref terminal terminalRef : ℝ}
    (hflow : initial+flow-derivative+entropy≤w-wref)
    (hflowTaylor : Aflow*ds+position+flowCurvature*ds^2-rankLoss*variation≤flow)
    (hterminalTaylor : Aterminal*ds+terminalCurvature*ds^2≤terminalRef-terminal)
    (hfeasible : w≤terminal) :
    (wref-terminalRef)+initial+(Aflow+Aterminal)*ds+position-derivative+entropy+
      (flowCurvature+terminalCurvature)*ds^2-rankLoss*variation≤0 := by
  nlinarith only [hflow,hflowTaylor,hterminalTaylor,hfeasible]

/-- This assembles the actual log-flow estimate with its two independently
certified Taylor bounds, then applies the proved Stieltjes coercivity theorem.
The scalar first variation and both boundary contributions remain visible. -/
theorem stieltjes_coercivity_from_log_flow (G : StieltjesFunction ℝ) {a b : ℝ}
    (hab : a≤b) (hleft : Function.leftLim G a=a) (hend : G b≤b)
    {f W : ℝ→ℝ} {W0 k Aflow Aterminal ds flowCurvature terminalCurvature rankLoss
      eps initial flow w wref terminal terminalRef : ℝ}
    (hf : IntegrableOn f (Icc a b))
    (hWlin : IntegrableOn (fun r=>W r*(deriv G r-1)) (Icc a b))
    (hW0 : 0≤W0) (hk : k≤0)
    (hW : ∀ᵐ r ∂volume.restrict (Icc a b),W0≤W r)
    (hpotential : ∀ r∈Icc a b,0<(∫ t in r..b,f t)-k-W0)
    (hxi : ∀ᵐ r ∂volume.restrict (Icc a b),0<deriv G r)
    (herr : IntegrableOn (fun r=>((∫ t in r..b,f t)-W r-k)^2/
      ((∫ t in r..b,f t)-k-W0)) (Icc a b))
    (hent : IntegrableOn (fun r=>W r*transportEntropy (deriv G r)) (Icc a b))
    (heps : (∫ r in Icc a b,((∫ t in r..b,f t)-W r-k)^2/
      ((∫ t in r..b,f t)-k-W0))≤eps)
    (hflow : initial+flow-(∫ r in Icc a b,W r*(deriv G r-1))+
      (∫ r in Icc a b,W r*transportEntropy (deriv G r))≤w-wref)
    (hflowTaylor : Aflow*ds+(∫ r in Icc a b,f r*(G r-r))+
      flowCurvature*ds^2-rankLoss*matchingVariation G a b≤flow)
    (hterminalTaylor : Aterminal*ds+terminalCurvature*ds^2≤terminalRef-terminal)
    (hfeasible : w≤terminal) :
    (wref-terminalRef)+initial-eps+(Aflow+Aterminal)*ds+
      (flowCurvature+terminalCurvature)*ds^2+k*(G b-b)+
      ((8:ℝ)/9*W0-rankLoss)*matchingVariation G a b≤0 := by
  exact stieltjes_reference_coercivity_linear G hab hleft hend hf hWlin hW0 hk hW
    hpotential hxi herr hent heps
    (transport_flow_terminal_combine hflow hflowTaylor hterminalTaylor hfeasible)

end OptimalG.Variational
