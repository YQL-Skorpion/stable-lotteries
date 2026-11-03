import OptimalG.VariationalTransportTaylor
import OptimalG.VariationalTransportIntegral

/-! Integration of the checked Schur form in B.4. The factor four comes
from the two rank coordinates, each controlled by 2(b-a) times variation. -/
namespace OptimalG.Variational
open Set MeasureTheory

 theorem segment_second_order_transport {f f' f'' : ℝ → ℝ}
    {ds e1 e2 ms mr : ℝ}
    (hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f' (f'' t) t)
    (hsecond : ∀ t ∈ Ioo (0:ℝ) 1, ms*ds^2-mr*(e1^2+e2^2) ≤ f'' t) :
    f 0+f' 0+(ms/2)*ds^2-(mr/2)*(e1^2+e2^2) ≤ f 1 := by
  have h := segment_second_order_lower hf hf' hsecond
  nlinarith only [h]

 theorem transport_rank_remainder {mr e1 e2 length V : ℝ}
    (hmr : 0 ≤ mr) (h1 : e1^2 ≤ 2*length*V) (h2 : e2^2 ≤ 2*length*V) :
    (mr/2)*(e1^2+e2^2) ≤ (mr/2)*(4*length*V) := by
  apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)

variable {X : Type*} [MeasurableSpace X]

/-- The Hessian error is reduced to the exact numerical integrals which
appear in the reference certificate. -/
theorem transport_integrated_taylor {mu : Measure X} {L Lin ms mr e1 e2 : X → ℝ}
    {ds length V : ℝ}
    (hL : Integrable L mu) (hLin : Integrable Lin mu)
    (hms : Integrable ms mu) (hmr : Integrable mr mu)
    (hmrpos : ∀ᵐ s ∂mu, 0 ≤ mr s)
    (he1 : ∀ᵐ s ∂mu, (e1 s)^2 ≤ 2*length*V)
    (he2 : ∀ᵐ s ∂mu, (e2 s)^2 ≤ 2*length*V)
    (hTaylor : ∀ᵐ s ∂mu,
      Lin s+(ms s/2)*ds^2-(mr s/2)*((e1 s)^2+(e2 s)^2) ≤ L s) :
    (∫ s, Lin s ∂mu)+((∫ s, ms s ∂mu)/2)*ds^2-
      (4*length*((∫ s, mr s ∂mu)/2))*V ≤ ∫ s, L s ∂mu := by
  have hb : Integrable (fun s => Lin s+ms s*(ds^2/2)-mr s*(2*length*V)) mu :=
    (hLin.add (hms.mul_const _)).sub (hmr.mul_const _)
  have hi := integral_mono_ae hb hL (by
    filter_upwards [hmrpos,he1,he2,hTaylor] with s hp h1 h2 ht
    have hh := transport_rank_remainder hp h1 h2
    nlinarith only [hh,ht])
  have hfirst : Integrable (fun s => Lin s+ms s*(ds^2/2)) mu := hLin.add (hms.mul_const _)
  rw [integral_sub hfirst (hmr.mul_const _),
    integral_add hLin (hms.mul_const _),integral_mul_const,integral_mul_const] at hi
  nlinarith only [hi]

/-- The endpoint's scalar curvature adds to the flow curvature. -/
theorem transport_scalar_and_rank_remainder {flow endGap linearFlow linearEnd ms mr endMs ds length V : ℝ}
    (hflow : linearFlow+(ms/2)*ds^2-(4*length*(mr/2))*V ≤ flow)
    (hend : linearEnd+(endMs/2)*ds^2 ≤ endGap) :
    linearFlow+linearEnd+((ms+endMs)/2)*ds^2-(4*length*(mr/2))*V ≤ flow+endGap := by
  nlinarith only [hflow,hend]

end OptimalG.Variational
