import OptimalG.MiddleRankConvexity
import OptimalG.VariationalRecovery

/-! The polynomial lower bound of C.27 follows directly by integrating the
fixed-control inequality once. No exponential approximation is needed. -/
namespace OptimalG
open Set
open Variational (quadratic)

theorem control_deficit_identity (lam S p theta alpha J r : ℝ) :
    lam-r-(-theta*(r-lam)-alpha*(quadratic lam (r-p)-S-J))=
      (theta-1+alpha*p)*(r-lam)-alpha*p^2/2+alpha*(quadratic lam r-S-J) := by
  unfold quadratic
  ring

theorem positive_part_deficit_growth {D E : ℝ→ℝ} {a b c m alpha : ℝ}
    (hc : c∈Icc a b) (hm : 0<m) (halpha : 0≤alpha)
    (hcont : ContinuousOn D (Icc a b))
    (hd : ∀ r∈Ioo a b,HasDerivAt D (E r) r)
    (hD : ∀ r∈Icc a b,0≤D r) (hE : ∀ r∈Icc a b,0≤E r)
    (hfield : ∀ r∈Icc a b,m*(r-c)+alpha*D r≤E r) :
    ∀ r∈Icc a b,max (m*(r-c)) 0+alpha/(2*m)*(max (m*(r-c)) 0)^2≤E r := by
  let F : ℝ→ℝ := fun r => D r-(m/2)*(r-c)^2
  have hsub : Icc c b⊆Icc a b := Icc_subset_Icc hc.1 le_rfl
  have hFcont : ContinuousOn F (Icc c b) := by
    have hDc := hcont.mono hsub
    dsimp [F]
    fun_prop
  have hFd (r : ℝ) (hr : r∈interior (Icc c b)) :
      HasDerivAt F (E r-m*(r-c)) r := by
    rw [interior_Icc] at hr
    have hrab : r∈Ioo a b := ⟨hc.1.trans_lt hr.1,hr.2⟩
    convert! (hd r hrab).sub ((((hasDerivAt_id r).sub_const c).pow 2).const_mul (m/2)) using 1 <;>
      simp [F] <;> ring
  have hmono : MonotoneOn F (Icc c b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hFcont
    · intro r hr
      exact (hFd r hr).hasDerivWithinAt
    · intro r hr
      have hrab := hsub (interior_subset hr)
      have hf := hfield r hrab
      have hp := mul_nonneg halpha (hD r hrab)
      linarith
  intro r hr
  by_cases hrc : r≤c
  · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos hm.le (sub_nonpos.mpr hrc))]
    simpa using hE r hr
  · have hcr := (lt_of_not_ge hrc).le
    have hg := hmono ⟨le_rfl,hc.2⟩ ⟨hcr,hr.2⟩ hcr
    have hDc := hD c hc
    have hbound : (m/2)*(r-c)^2≤D r := by
      dsimp [F] at hg
      nlinarith only [hg,hDc]
    have hscaled := mul_le_mul_of_nonneg_left hbound halpha
    have hf := hfield r hr
    have halg : alpha/(2*m)*(m*(r-c))^2=alpha*((m/2)*(r-c)^2) := by
      field_simp [ne_of_gt hm] <;> ring
    rw [max_eq_left (mul_nonneg hm.le (sub_nonneg.mpr hcr)),halg]
    linarith only [hscaled,hf]

namespace VerifierCurve

/-- A fixed control gives the actual high-score deficit bound used in the
large-mass interval checks, including the quadratic improvement. -/
theorem fixedControl_deficit_lower {phi : ℝ→ℝ} {lam S p theta alpha a b c : ℝ}
    (h : VerifierCurve phi lam) (ha : 0≤a) (hb : b≤1)
    (hc : c∈Icc a b) (hm : 0<theta-1+alpha*p) (halpha : 0≤alpha)
    (hzero : (theta-1+alpha*p)*(c-lam)=alpha*p^2/2)
    (hD : ∀ r∈Icc a b,0≤quadratic lam r-S-curvePrimitive phi r)
    (hcontrol : ∀ r∈Icc a b,phi r≤
      -theta*(r-lam)-alpha*(quadratic lam (r-p)-S-curvePrimitive phi r)) :
    ∀ r∈Icc a b,
      max ((theta-1+alpha*p)*(r-lam)-alpha*p^2/2) 0+
        alpha/(2*(theta-1+alpha*p))*
          (max ((theta-1+alpha*p)*(r-lam)-alpha*p^2/2) 0)^2≤lam-r-phi r := by
  have hs : Icc a b⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  have hDc : ContinuousOn (fun r => quadratic lam r-S-curvePrimitive phi r) (Icc a b) := by
    have hJ := h.primitive_continuous.mono hs
    unfold quadratic
    fun_prop
  have hd (r : ℝ) (hr : r∈Ioo a b) :
      HasDerivAt (fun u => quadratic lam u-S-curvePrimitive phi u) (lam-r-phi r) r := by
    have hJ := h.primitive_hasDerivAt ⟨ha.trans_lt hr.1,hr.2.trans_le hb⟩
    exact ((Variational.quadratic_hasDerivAt lam r).sub_const S).sub hJ
  have hE (r : ℝ) (hr : r∈Icc a b) : 0≤lam-r-phi r := by
    have hh := h.ceiling r (hs hr)
    linarith
  have hlin (r : ℝ) : (theta-1+alpha*p)*(r-c)=
      (theta-1+alpha*p)*(r-lam)-alpha*p^2/2 := by nlinarith only [hzero]
  have hfield (r : ℝ) (hr : r∈Icc a b) :
      (theta-1+alpha*p)*(r-c)+alpha*(quadratic lam r-S-curvePrimitive phi r)≤lam-r-phi r := by
    rw [hlin,← control_deficit_identity]
    linarith only [hcontrol r hr]
  have hh := positive_part_deficit_growth hc hm halpha hDc hd hD hE hfield
  simpa only [hlin] using hh

end VerifierCurve
end OptimalG
