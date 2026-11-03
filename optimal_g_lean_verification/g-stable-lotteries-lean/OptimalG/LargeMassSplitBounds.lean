import OptimalG.ExtendedSlackProfiles

/-! Three elementary split reductions for the large-mass mixed test: an
exact cap remainder, a full concave square, and the three possible extrema
of the affine forward-area envelope. -/
namespace OptimalG
open Set Variational

theorem capDeficit_quadratic_remainder {lam S x q : ℝ} (hx : x≠1) (hq : q≠1) :
    capDeficit lam S q=capDeficit lam S x-capSlack lam S x*(q-x)+
      (q-x)^2*(1/2-lam*S/((1-q)*(1-x)^2)) := by
  have hx' : 1-x≠0 := sub_ne_zero.mpr hx.symm
  have hq' : 1-q≠0 := sub_ne_zero.mpr hq.symm
  unfold capDeficit capSlack cap capScore quadratic
  field_simp [hx',hq']
  ring

theorem capDeficit_quadratic_floor {lam S q : ℝ}
    (hprod : lam*S≤3/200) (hq : q∈Icc (527/2000:ℝ) (1459/5000)) :
    capDeficit lam S (527/2000)-capSlack lam S (527/2000)*(q-527/2000)+
      (9/20)*(q-527/2000)^2≤capDeficit lam S q := by
  have hden : (3/10:ℝ)≤(1-q)*(1-(527/2000:ℝ))^2 := by
    nlinarith only [hq.2]
  have hden0 : 0<(1-q)*(1-(527/2000:ℝ))^2 := by linarith only [hden]
  have hfrac : lam*S/((1-q)*(1-(527/2000:ℝ))^2)≤1/20 := by
    rw [div_le_iff₀ hden0]
    nlinarith only [hprod,hden]
  rw [capDeficit_quadratic_remainder (by norm_num : (527/2000:ℝ)≠1)
    (by linarith only [hq.2] : q≠1)]
  have hm := mul_nonneg (sq_nonneg (q-527/2000)) (sub_nonneg.mpr hfrac)
  nlinarith only [hm]

theorem concave_quadratic_nonpos {A B C x : ℝ} (hC : 0<C)
    (hc : 4*C*A+B^2≤0) : A+B*x-C*x^2≤0 := by
  have hs := sq_nonneg (B-2*C*x)
  have hid : (4*C)*(A+B*x-C*x^2)=4*C*A+B^2-(B-2*C*x)^2 := by ring
  have hn : (4*C)*(A+B*x-C*x^2)≤0 := by rw [hid];linarith only [hc,hs]
  exact nonpos_of_mul_nonpos_right hn (by positivity)

theorem cap_split_nonpos {A B flat p q lam S : ℝ}
    (hp : 0<p) (hprod : lam*S≤3/200)
    (hq : q∈Icc (527/2000:ℝ) (1459/5000))
    (hc : 2*p*(9/10)*(A+B*(527/2000)+p*(flat-capDeficit lam S (527/2000)))+
      (B+p*capSlack lam S (527/2000))^2≤0) :
    A+B*q+p*(flat-capDeficit lam S q)≤0 := by
  have hf := capDeficit_quadratic_floor hprod hq
  have hm := mul_le_mul_of_nonneg_left hf hp.le
  have hs := concave_quadratic_nonpos
    (A:=A+B*(527/2000)+p*(flat-capDeficit lam S (527/2000)))
    (B:=B+p*capSlack lam S (527/2000)) (C:=p*(9/20)) (x:=q-527/2000)
    (by positivity) (by convert! hc using 1 <;> ring)
  nlinarith only [hm,hs]

noncomputable def forwardSplitEnvelope (A B p E sigma w q : ℝ) : ℝ :=
  A+B*q-p*max 0 (E-sigma*(q-w))

private theorem affine_nonpos {A B a b q : ℝ} (hq : q∈Icc a b)
    (ha : A+B*a≤0) (hb : A+B*b≤0) : A+B*q≤0 := by
  by_cases hB : 0≤B
  · have hm := mul_le_mul_of_nonneg_left hq.2 hB
    linarith only [hm,hb]
  · have hm := mul_le_mul_of_nonpos_left hq.1 (le_of_not_ge hB)
    linarith only [hm,ha]

/-- An affine function minus a positive-part affine area is controlled by
its two interval endpoints and its sole breakpoint, even if the breakpoint
is outside the interval. -/
theorem forwardSplitEnvelope_nonpos {A B p E sigma w top : ℝ}
    (hs : 0<sigma)
    (hl : forwardSplitEnvelope A B p E sigma w w≤0)
    (hr : forwardSplitEnvelope A B p E sigma w top≤0)
    (hk : forwardSplitEnvelope A B p E sigma w (w+E/sigma)≤0) :
    ∀ q∈Icc w top,forwardSplitEnvelope A B p E sigma w q≤0 := by
  let k := w+E/sigma
  have he (q : ℝ) : E-sigma*(q-w)=sigma*(k-q) := by
    dsimp [k]
    field_simp [hs.ne']
    ring
  have hleft {q : ℝ} (hq : q≤k) : forwardSplitEnvelope A B p E sigma w q=
      (A-p*(E+sigma*w))+(B+p*sigma)*q := by
    unfold forwardSplitEnvelope
    rw [max_eq_right (by rw [he];exact mul_nonneg hs.le (sub_nonneg.mpr hq))]
    ring
  have hright {q : ℝ} (hq : k≤q) : forwardSplitEnvelope A B p E sigma w q=A+B*q := by
    unfold forwardSplitEnvelope
    rw [max_eq_left (by rw [he];exact mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr hq))]
    ring
  intro q hq
  by_cases hqk : q≤k
  · rw [hleft hqk]
    have hwl := hq.1.trans hqk
    by_cases htk : top≤k
    · apply affine_nonpos hq
      · rwa [hleft hwl] at hl
      · rwa [hleft htk] at hr
    · apply affine_nonpos (a:=w) (b:=k) ⟨hq.1,hqk⟩
      · rwa [hleft hwl] at hl
      · change forwardSplitEnvelope A B p E sigma w k≤0 at hk
        rwa [hleft le_rfl] at hk
  · have hkq := le_of_not_ge hqk
    rw [hright hkq]
    have hkt := hkq.trans hq.2
    by_cases hkw : k≤w
    · apply affine_nonpos hq
      · rwa [hright hkw] at hl
      · rwa [hright hkt] at hr
    · apply affine_nonpos (a:=k) (b:=top) ⟨hkq,hq.2⟩
      · change forwardSplitEnvelope A B p E sigma w k≤0 at hk
        rwa [hright le_rfl] at hk
      · rwa [hright hkt] at hr

end OptimalG
