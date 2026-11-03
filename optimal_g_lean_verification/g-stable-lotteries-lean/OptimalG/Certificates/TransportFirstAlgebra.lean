import OptimalG.Certificates.TransportHessianCalculus

/-! Combining weighted logarithmic derivatives before enclosure removes
interval dependency. This is an exact identity for the same actual
coefficients and directional derivatives used in the transport Taylor proof. -/
namespace OptimalG.Certificates
open scoped BigOperators
namespace RatExpr

theorem factored_log_partial {n : ℕ} (a b c d : RatExpr n) (i : Fin n)
    (x : Fin n→ℝ) (ha : a.eval x≠0) (hb : b.eval x≠0)
    (hc : c.eval x≠0) (hd : d.eval x≠0) :
    (a*b*c/d).eval x*((logPartial i a).eval x+(logPartial i b).eval x+
      (logPartial i c).eval x-(logPartial i d).eval x)=
      (partialExpr i (a*b*c/d)).eval x := by
  change ((a.eval x*b.eval x*c.eval x)*(d.eval x)⁻¹)*
      ((logPartial i a).eval x+(logPartial i b).eval x+
        (logPartial i c).eval x-(logPartial i d).eval x)=
      (partialExpr i (.mul (.mul (.mul a b) c) (.inv d))).eval x
  simp only [logPartial_eval,partial_mul_eval,partial_inv_eval,eval]
  field_simp
  ring

end RatExpr
namespace Transport.FrozenParameters
open RatExpr

noncomputable def coordinateDirection (j : Fin 16) : Fin 16→ℝ :=
  fun i => if i=j then 1 else 0

theorem logGradient_coordinate (e : E) (x : Fin 16→ℝ) (j : Fin 16) :
    logGradient e x (coordinateDirection j)=(logPartial j e).eval x := by
  simp [logGradient,coordinateDirection]

theorem coefficient_mul_sourceFirst (d : FrozenParameters) (late : Bool)
    (i : Fin 4) (j : Fin 16) (x : Fin 16→ℝ) (hr : d.sourceRegular late i x) :
    (d.coefficients late i).eval x*d.sourceFirst late i x (coordinateDirection j)=
      (partialExpr j (d.coefficients late i)).eval x := by
  rcases hr with ⟨_,hj,_,hn,_,hm,_,hD⟩
  simpa only [coefficients,sourceFirst,logGradient_coordinate] using
    factored_log_partial d.j (d.numerators late i) (d.score i) (d.denominator late)
      j x hj hn hm hD

/-- This is the finite cancellation behind both the scalar first variation
and the two rank flux densities. The reference weight factor is kept explicit. -/
theorem weightedFirst_combined (d : FrozenParameters) (late : Bool)
    (x : Fin 16→ℝ) (j : Fin 16) (factor : ℝ) (power weights : Fin 4→ℝ)
    (hregular : ∀ i∈activeTerms late,d.sourceRegular late i x)
    (hweight : ∀ i∈activeTerms late,weights i=factor*power i*(d.coefficients late i).eval x) :
    d.weightedFirst late weights x (coordinateDirection j)=
      factor*∑ i∈activeTerms late,power i*(partialExpr j (d.coefficients late i)).eval x := by
  unfold weightedFirst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hweight i hi]
  calc
    factor*power i*(d.coefficients late i).eval x*d.sourceFirst late i x (coordinateDirection j)=
        factor*(power i*((d.coefficients late i).eval x*d.sourceFirst late i x (coordinateDirection j))) := by ring
    _=factor*(power i*(partialExpr j (d.coefficients late i)).eval x) := by
      rw [coefficient_mul_sourceFirst d late i j x (hregular i hi)]

end Transport.FrozenParameters
end OptimalG.Certificates
