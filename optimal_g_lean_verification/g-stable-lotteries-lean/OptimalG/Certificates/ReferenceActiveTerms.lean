import OptimalG.Certificates.TransportHessianCalculus
import OptimalG.VariationalTransportSource

/-! The active Hessian sum is exactly the four-term transport sum. On the
early branch, the two omitted reference coefficients and their weights are
identically zero, so no limiting convention or positive perturbation is used.
-/
namespace OptimalG.Certificates.Transport.FrozenParameters
open Real Variational

theorem sum_activeTerms_eq_sum (late : Bool) (f : Fin 4→ℝ)
    (hz : late=false→f 0=0 ∧ f 2=0) : (∑ i∈activeTerms late,f i)=∑ i,f i := by
  cases late
  · obtain ⟨h0,h2⟩ := hz rfl
    have h13 : (1:Fin 4)≠3 := by decide
    have hsucc : Fin.succ (2:Fin 3)=(3:Fin 4) := rfl
    simp [activeTerms,Fin.sum_univ_succ,h0,h2,h13,hsucc,Finset.sum_insert,Finset.sum_singleton]
  · simp only [activeTerms,if_true]

theorem active_weighted_sum_eq_sum (late : Bool) (w f : Fin 4→ℝ)
    (hz : late=false→w 0=0 ∧ w 2=0) :
    (∑ i∈activeTerms late,w i*f i)=∑ i,w i*f i := by
  apply sum_activeTerms_eq_sum
  intro he
  obtain ⟨h0,h2⟩ := hz he
  simp only [h0,h2,zero_mul,and_self]

theorem transportCoefficientSource_eq_active {late : Bool} {s : ℝ}
    {rho w0 : ℝ→ℝ} {a a0 : ℝ→Fin 4→ℝ} {delta : Fin 4→ℝ} {w : Fin 4→ℝ}
    (hw : ∀ i,w i=rho s*referenceWeight (a0 s i) (delta i) (w0 s))
    (hz : late=false→a0 s 0=0 ∧ a0 s 2=0) :
    transportCoefficientSource rho w0 a a0 delta s=
      ∑ i∈activeTerms late,w i*log (a s i/a0 s i) := by
  rw [active_weighted_sum_eq_sum late w _ (by
    intro he
    obtain ⟨h0,h2⟩ := hz he
    rw [hw 0,hw 2]
    simp only [referenceWeight,h0,h2,zero_mul,mul_zero,and_self])]
  simp only [transportCoefficientSource,hw,Finset.mul_sum,mul_assoc]

end OptimalG.Certificates.Transport.FrozenParameters
