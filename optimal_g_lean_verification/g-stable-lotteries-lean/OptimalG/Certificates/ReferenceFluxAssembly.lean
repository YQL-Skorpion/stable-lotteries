import OptimalG.Certificates.ReferenceFluxCell

/-! An accepted rank partition accumulates the actual absorption-error
integrals.  The final scalar budget is checked using the integer endpoints,
so no floating-point sum or inferred quadrature identity is used. -/
namespace OptimalG.Certificates
open MeasureTheory

theorem cumulativeIntegralCheck_cell_order {s : ℕ} {start finish : ℚ}
    {cells : List IntegralCell}
    (hc : cumulativeIntegralCheck s start finish cells=true)
    {c : IntegralCell} (hmem : c∈cells) : c.lo<c.hi := by
  induction cells generalizing start with
  | nil => simp at hmem
  | cons a cs ih =>
    have hh : (a.lo=start ∧ a.lo<a.hi) ∧
        (totalBox cs).subsetCheck a.future=true ∧
        cumulativeIntegralCheck s a.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    rcases List.mem_cons.mp hmem with he|hm
    · subst c
      exact hh.1.2
    · exact ih hh.2.2 hm

theorem cumulativeIntegralCheck_sum_upper {s : ℕ} {start finish : ℚ}
    {cells : List IntegralCell} {f : ℝ→ℝ} (upper : IntegralCell→ℤ)
    (hc : cumulativeIntegralCheck s start finish cells=true)
    (hf : ∀ c∈cells,IntervalIntegrable f volume (c.lo:ℝ) c.hi ∧
      (s:ℝ)*(∫ r in (c.lo:ℝ)..c.hi,f r)≤(upper c:ℝ)) :
    IntervalIntegrable f volume (start:ℝ) finish ∧
      (s:ℝ)*(∫ r in (start:ℝ)..finish,f r)≤((cells.map upper).sum:ℤ) := by
  induction cells generalizing start with
  | nil =>
    have he : start=finish := by
      simpa only [cumulativeIntegralCheck,decide_eq_true_eq] using hc
    subst start
    simp
  | cons c cs ih =>
    have hh : (c.lo=start ∧ c.lo<c.hi) ∧
        (totalBox cs).subsetCheck c.future=true ∧
        cumulativeIntegralCheck s c.hi finish cs=true := by
      simpa only [cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
    obtain ⟨hi,hu⟩ := hf c (by simp)
    obtain ⟨hti,htu⟩ := ih hh.2.2 (fun d hd => hf d (by simp [hd]))
    rw [←hh.1.1]
    refine ⟨hi.trans hti,?_⟩
    rw [←intervalIntegral.integral_add_adjacent_intervals hi hti,mul_add]
    simpa only [List.map_cons,List.sum_cons,Int.cast_add] using add_le_add hu htu

namespace Transport.ReferenceFluxCell

def errorBudgetCheck (s : ℕ) (budget : ℚ) (cells : List ReferenceFluxCell) : Bool :=
  decide ((((cells.map (fun c=>c.errorMass.hi)).sum:ℤ):ℚ)<budget*(s:ℚ))

theorem checked_error_budget {s k : ℕ} (hs : 0<s) {start finish budget : ℚ}
    (cells : List ReferenceFluxCell)
    (hchecks : cells.all (fun c=>c.check s k)=true)
    (hcover : cumulativeIntegralCheck s start finish (cells.map (·.interval))=true)
    (hbudget : errorBudgetCheck s budget cells=true)
    {e : ℝ→ℝ}
    (he : ∀ c∈cells,IntervalIntegrable e volume (c.interval.lo:ℝ) c.interval.hi)
    (hb : ∀ c∈cells,∀ᵐ r ∂volume.restrict (Set.Icc (c.interval.lo:ℝ) c.interval.hi),
      c.error.Contains s (e r)) :
    IntervalIntegrable e volume (start:ℝ) finish ∧
      (∫ r in (start:ℝ)..finish,e r)<(budget:ℝ) := by
  -- The mass bound belongs to the full flux cell, while coverage uses only
  -- its interval.  Induction keeps this association exact.
  have sum_bound : ∀ (cs : List ReferenceFluxCell) (a : ℚ),
      cumulativeIntegralCheck s a finish (cs.map (·.interval))=true →
      (∀ c∈cs,IntervalIntegrable e volume (c.interval.lo:ℝ) c.interval.hi ∧
        (s:ℝ)*(∫ r in (c.interval.lo:ℝ)..c.interval.hi,e r)≤(c.errorMass.hi:ℝ)) →
      IntervalIntegrable e volume (a:ℝ) finish ∧
        (s:ℝ)*(∫ r in (a:ℝ)..finish,e r)≤((cs.map (fun c=>c.errorMass.hi)).sum:ℤ) := by
    intro cs
    induction cs with
    | nil =>
      intro a hc _
      have ha : a=finish := by
        simpa only [List.map_nil,cumulativeIntegralCheck,decide_eq_true_eq] using hc
      subst a
      simp
    | cons c cs ih =>
      intro a hc hf
      have hh : (c.interval.lo=a ∧ c.interval.lo<c.interval.hi) ∧
          (totalBox (cs.map (·.interval))).subsetCheck c.interval.future=true ∧
          cumulativeIntegralCheck s c.interval.hi finish (cs.map (·.interval))=true := by
        simpa only [List.map_cons,cumulativeIntegralCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
      obtain ⟨hi,hu⟩ := hf c (by simp)
      obtain ⟨hti,htu⟩ := ih c.interval.hi hh.2.2 (fun d hd=>hf d (by simp [hd]))
      rw [←hh.1.1]
      refine ⟨hi.trans hti,?_⟩
      rw [←intervalIntegral.integral_add_adjacent_intervals hi hti,mul_add]
      simpa only [List.map_cons,List.sum_cons,Int.cast_add] using add_le_add hu htu
  have hcell : ∀ c∈cells,IntervalIntegrable e volume (c.interval.lo:ℝ) c.interval.hi ∧
      (s:ℝ)*(∫ r in (c.interval.lo:ℝ)..c.interval.hi,e r)≤(c.errorMass.hi:ℝ) := by
    intro c hc
    have hcheck := List.all_eq_true.mp hchecks c hc
    have horder := cumulativeIntegralCheck_cell_order hcover (List.mem_map.mpr ⟨c,hc,rfl⟩)
    exact ⟨he c hc,(checked_error_mass hs c hcheck horder.le (he c hc) (hb c hc)).2⟩
  obtain ⟨hi,hu⟩ := sum_bound cells start hcover hcell
  have hbudget' : (((cells.map (fun c=>c.errorMass.hi)).sum:ℤ):ℝ)<(budget:ℝ)*(s:ℝ) := by
    exact_mod_cast (of_decide_eq_true hbudget :
      (((cells.map (fun c=>c.errorMass.hi)).sum:ℤ):ℚ)<budget*(s:ℚ))
  refine ⟨hi,?_⟩
  have hs' : (0:ℝ)<s := by exact_mod_cast hs
  nlinarith

end Transport.ReferenceFluxCell
end OptimalG.Certificates
