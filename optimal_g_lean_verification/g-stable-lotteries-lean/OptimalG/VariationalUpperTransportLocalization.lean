import OptimalG.VariationalTransferredLocalization
import OptimalG.VariationalTransferredMatching

/-! All four optimizer-localization inputs follow together from the actual
upper-reference transport inequality. The matching atoms and the initial
high-rank logarithmic deficit are retained; no continuity of the competing
score is assumed. The finite reference estimates remain explicit premises. -/
namespace OptimalG.Variational
open Set MeasureTheory ParameterTransfer

theorem original_localizations_of_upper_transport
    {lam delta reference rho Z A k : ℝ} {d : LowRankData} {Y Xi : ℝ→ℝ}
    (hd : Admissible lam d) (hLnew : Certificates.Compact.LambdaRange (lam+delta))
    (hdelta : delta∈Icc (0:ℝ) 0.00000003)
    (hY : IsContinuation lam d Y) (hpass : PassesTerminalTests lam d Y)
    (T : UpwardTransfer lam delta d Y)
    (G : StieltjesFunction ℝ) (href : reference∈Icc (0.29509:ℝ) 0.296)
    (hleft : Function.leftLim G reference=reference)
    (hmatch : ∀ r∈Icc reference (0.34854007977695545:ℝ),
      G r∈Icc reference (0.34854007977695545:ℝ) ∧
      shiftedPrimitive lam d delta (G r)=Xi r)
    (hXiLeft : Xi reference=cap (lam+delta) (scalar d.S delta) reference)
    (hXiRight : Xi (0.34854007977695545:ℝ)=
      quadratic (lam+delta) 0.34854007977695545-scalar d.S delta)
    (hrho : (0.07:ℝ)≤rho) (hZ : 0<Z) (hZmax : Z≤(0.00136:ℝ))
    (hA : |A|≤(0.00011:ℝ)) (hk : k≤-(16:ℝ))
    (htransport :
      rho*Real.log (1+(quadratic (lam+delta) (7835342428237777/10^16)-
        scalar d.S delta-T.trajectory (7835342428237777/10^16))/Z)+
      A*(scalar d.S delta-(2303623505254907/100000000000000000:ℝ))+
      54*(scalar d.S delta-(2303623505254907/100000000000000000:ℝ))^2+
      k*(G 0.34854007977695545-0.34854007977695545)+
      0.64*matchingVariation G reference 0.34854007977695545≤(0.000003:ℝ)) :
    d.S∈Icc (0.02271790:ℝ) 0.023354 ∧
      cap lam d.S reference-lowPrimitive lam d reference<(0.00000191061404:ℝ) ∧
      d.S-quadratic lam 0.34854007977695545+lowPrimitive lam d 0.34854007977695545<
        (0.00000008688098:ℝ) ∧
      quadratic lam (7835342428237777/10^16)-d.S-Y (7835342428237777/10^16)<
        (1711874:ℝ)/10^13 := by
  have hab : reference≤(0.34854007977695545:ℝ) := by linarith only [href.2]
  have hE : 0≤quadratic (lam+delta) (7835342428237777/10^16)-scalar d.S delta-
      T.trajectory (7835342428237777/10^16) :=
    sub_nonneg.mpr (T.upper _ (by norm_num [zStart,zEnd]))
  have hi := initial_log_deficit_nonneg (show 0≤rho by linarith only [hrho]) hZ hE
  have heb : G 0.34854007977695545-0.34854007977695545≤0 :=
    sub_nonpos.mpr (hmatch _ ⟨hab,le_rfl⟩).1.2
  have hloc := upper_transport_localization hi hA hk heb
    (matchingVariation_nonneg G _ _) htransport
  have hJ : LipschitzOnWith (1/3:NNReal) (shiftedPrimitive lam d delta)
      (Icc reference (0.34854007977695545:ℝ)) := (transferred_low_lipschitz hd).mono
    (Icc_subset_Icc (by norm_num [ell]; linarith only [href.1]) (by norm_num [xHi]))
  have hlow := upper_transport_initial_primitive G hab hleft hJ hmatch hloc.2.1
  rw [hXiLeft] at hlow
  have htail := upper_transport_terminal_primitive hab hJ hmatch
    (by linarith only [hloc.2.2.1])
  rw [hXiRight] at htail
  have hhigh := initial_high_deficit_lt_6e8 hrho hZ hZmax hE hloc.2.2.2
  exact original_localizations_of_transferred hd hLnew hdelta hY hpass T href
    hloc.1 hlow (by linarith only [htail]) hhigh

end OptimalG.Variational
