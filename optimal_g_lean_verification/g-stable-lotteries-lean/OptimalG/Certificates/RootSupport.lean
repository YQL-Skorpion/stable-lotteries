import OptimalG.Certificates.Control

/-! Supporting-line certificates bound all independent root controls at once.
The displayed inequalities are for the actual score values, not sampled values. -/
namespace OptimalG.Certificates.Control

/-- Two balanced upper supporting lines imply a lower bound on the rational
control for every independent choice of its two root coordinates. -/
theorem lower_of_support_lines (U L p R P K C alpha x y Ax By : ℝ)
    (hD : 0<det (2*L-x) (p+y-L) R P)
    (hx : 0≤cx U (p+y-L) R K) (hy : 0≤cy U (2*L-x) P K)
    (hsx : Ax+C*x≤2*L*C-alpha*P)
    (hsy : By+C*y≤(L-p)*C+alpha*R) :
    -U*C-K*alpha≤value U (2*L-x) (p+y-L) R P K Ax By := by
  have h1 := mul_le_mul_of_nonneg_left (show Ax≤2*L*C-alpha*P-C*x by linarith) hx
  have h2 := mul_le_mul_of_nonneg_left (show By≤(L-p)*C+alpha*R-C*y by linarith) hy
  have he : cx U (p+y-L) R K*(2*L*C-alpha*P-C*x)+
      cy U (2*L-x) P K*((L-p)*C+alpha*R-C*y)=
      det (2*L-x) (p+y-L) R P*(U*C+K*alpha) := by
    unfold cx cy det
    ring
  have hn : U*(R*Ax+P*By)+K*alphaNumerator (2*L-x) (p+y-L) Ax By ≤
      det (2*L-x) (p+y-L) R P*(U*C+K*alpha) := by
    have hh := add_le_add h1 h2
    rw [he] at hh
    unfold cx cy alphaNumerator at *
    nlinarith only [hh]
  unfold value
  apply (le_div_iff₀ hD).mpr
  nlinarith only [hn]

/-- A tangent supporting both score domains needs only a one-sided balance
inequality. Thus exact rational points just beyond the optimizing root can be
used without assuming an exact numerical root exists. -/
theorem lower_of_common_support (U L p R P K C a b A B x y Ax By : ℝ)
    (hR : 0<R)
    (hD : 0<det (2*L-x) (p+y-L) R P)
    (hx : 0≤cx U (p+y-L) R K) (hy : 0≤cy U (2*L-x) P K)
    (hsx : Ax+C*x≤A+C*a) (hsy : By+C*y≤B+C*b)
    (hbalance : R*A+P*B≤C*det (2*L-a) (p+b-L) R P) :
    -U*C-K*((B+C*(p+b-L))/R)≤value U (2*L-x) (p+y-L) R P K Ax By := by
  apply lower_of_support_lines U L p R P K C ((B+C*(p+b-L))/R) x y Ax By hD hx hy
  · apply hsx.trans
    have hquot : ((B+C*(p+b-L))/R)*R=B+C*(p+b-L) := div_mul_cancel₀ _ (ne_of_gt hR)
    apply (mul_le_mul_iff_of_pos_right hR).mp
    have hpq : ((B+C*(p+b-L))/R*P)*R=(B+C*(p+b-L))*P := by
      calc
        _ = ((B+C*(p+b-L))/R*R)*P := by ring
        _ = _ := by rw [hquot]
    rw [sub_mul,hpq]
    unfold det at hbalance
    nlinarith only [hbalance]
  · rw [div_mul_cancel₀ _ (ne_of_gt hR)]
    linarith

/-- Upward-rounded coefficient bounds preserve the conservative lower field
when both geometric multipliers are nonnegative. -/
theorem lower_of_coefficient_enclosures {U K C alpha Cu au H : ℝ}
    (hU : 0≤U) (hK : 0≤K) (hC : C≤Cu) (ha : alpha≤au)
    (hH : -U*C-K*alpha≤H) : -U*Cu-K*au≤H := by
  have h1 := mul_le_mul_of_nonneg_left hC hU
  have h2 := mul_le_mul_of_nonneg_left ha hK
  linarith

end OptimalG.Certificates.Control
