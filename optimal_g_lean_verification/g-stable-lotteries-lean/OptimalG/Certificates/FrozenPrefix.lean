import OptimalG.Certificates.ExpressionPrefix
import OptimalG.Certificates.TransportHessianCalculus

/-! Every actual transport coefficient uses coordinates0..11 only. The last
four slots merely store the external reference weights. -/
namespace OptimalG.Certificates.RatExpr
variable {n k : ℕ}
@[simp] theorem usesPrefix_addNotation (e f : RatExpr n) :
    (e+f).UsesPrefix k ↔ e.UsesPrefix k ∧ f.UsesPrefix k := Iff.rfl
@[simp] theorem usesPrefix_mulNotation (e f : RatExpr n) :
    (e*f).UsesPrefix k ↔ e.UsesPrefix k ∧ f.UsesPrefix k := Iff.rfl
@[simp] theorem usesPrefix_subNotation (e f : RatExpr n) :
    (e-f).UsesPrefix k ↔ e.UsesPrefix k ∧ f.UsesPrefix k := Iff.rfl
@[simp] theorem usesPrefix_divNotation (e f : RatExpr n) :
    (e/f).UsesPrefix k ↔ e.UsesPrefix k ∧ f.UsesPrefix k := Iff.rfl
@[simp] theorem usesPrefix_natNotation (m : ℕ) :
    (OfNat.ofNat m : RatExpr n).UsesPrefix k := True.intro
end OptimalG.Certificates.RatExpr

namespace OptimalG.Certificates.Transport.FrozenParameters
open RatExpr

 theorem coefficient_factors_prefix (d : FrozenParameters) (late : Bool) (i : Fin 4) :
    d.j.UsesPrefix 12 ∧ (d.numerators late i).UsesPrefix 12 ∧
      (d.score i).UsesPrefix 12 ∧ (d.denominator late).UsesPrefix 12 := by
  cases late <;> fin_cases i <;>
    norm_num [UsesPrefix,j,numerators,score,denominator,hExpr,kExpr,R,z,Pexpr,Kexpr,
      mR,mA,shift,Q,S,r,a,Fin.ext_iff]

theorem logGradient_prefix {e : E} (he : e.UsesPrefix 12) {x y : Fin 16→ℝ}
    (hxy : ∀ i,i.val<12→x i=y i) (v : Fin 16→ℝ) :
    logGradient e x v=logGradient e y v := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [prefix_eval_eq (prefix_logPartial he i) hxy]

theorem sourceRegular_prefix (d : FrozenParameters) (late : Bool) (i : Fin 4)
    {x y : Fin 16→ℝ} (hxy : ∀ j,j.val<12→x j=y j) :
    d.sourceRegular late i x↔d.sourceRegular late i y := by
  obtain ⟨hj,hn,hm,hD⟩ := coefficient_factors_prefix d late i
  simp only [sourceRegular,prefix_valid_iff hj hxy,prefix_valid_iff hn hxy,
    prefix_valid_iff hm hxy,prefix_valid_iff hD hxy,prefix_eval_eq hj hxy,
    prefix_eval_eq hn hxy,prefix_eval_eq hm hxy,prefix_eval_eq hD hxy]

theorem sourceFirst_prefix (d : FrozenParameters) (late : Bool) (i : Fin 4)
    {x y : Fin 16→ℝ} (hxy : ∀ j,j.val<12→x j=y j) (v : Fin 16→ℝ) :
    d.sourceFirst late i x v=d.sourceFirst late i y v := by
  obtain ⟨hj,hn,hm,hD⟩ := coefficient_factors_prefix d late i
  simp only [sourceFirst,logGradient_prefix hj hxy v,logGradient_prefix hn hxy v,
    logGradient_prefix hm hxy v,logGradient_prefix hD hxy v]

theorem weightedFirst_prefix (d : FrozenParameters) (late : Bool) (w : Fin 4→ℝ)
    {x y : Fin 16→ℝ} (hxy : ∀ j,j.val<12→x j=y j) (v : Fin 16→ℝ) :
    d.weightedFirst late w x v=d.weightedFirst late w y v := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [sourceFirst_prefix d late i hxy v]

end OptimalG.Certificates.Transport.FrozenParameters
