import OptimalG.VariationalContactTailAlgebra
import OptimalG.TailContact
import OptimalG.Certificates.VariationalBridge

/-! The quadratic tail's concavity follows from actual terminal tangency and
admissibility. It does not require a separate interval certificate. -/
namespace OptimalG.Variational
open Set

theorem Admissible.capSlack_positive_before_ell {lam q : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hq : q≤ell) : 0<capSlack lam d.S q := by
  have hL := hd.compact_lambdaRange
  have hfrac : 0≤lam*d.S/(1-q)^2 := div_nonneg
    (mul_nonneg (by linarith only [hL.1]) (by linarith [hd.slack_lower])) (sq_nonneg _)
  unfold capSlack capScore
  norm_num [ell] at hq
  linarith only [hL.1,hq,hfrac]

theorem Admissible.capDeficit_nonneg_before_ell {lam q : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hq : q∈Icc pLo ell) : 0≤capDeficit lam d.S q := by
  have hp := hd.primitive_lower ⟨hq.1,hq.2.trans (by norm_num [ell,zStart])⟩
  rw [primitive,if_pos hq.2] at hp
  unfold capDeficit
  linarith only [hp]

theorem Admissible.tailTwo_nonpos_of_contact {lam q b Y H : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hq : q∈Icc pLo ell) (hb : b∈Ioo (0:ℝ) 1)
    (hc : (1-b)^2=2*(lam-q)*capSlack lam d.S q-2*capDeficit lam d.S q)
    (hvalue : Y=b*((1-b)-capSlack lam d.S q))
    (hscore : H=1-2*b-capSlack lam d.S q+b*(1-b)/(lam-q)) :
    tailTwo b Y H≤0 := by
  have hL := hd.compact_lambdaRange
  have ha : 0<lam-q := by have h := hq.2; norm_num [ell] at h; linarith only [hL.1,h]
  have hh := contact_tailTwo_nonpos ha (sub_pos.mpr hb.2)
    (by linarith only [hb.1] : 1-b≤1)
    (hd.capSlack_positive_before_ell hq.2).le (hd.capDeficit_nonneg_before_ell hq) hc
  have he : 1-(1-b)=b := by ring
  rw [he] at hh
  have hs : -1+2*(1-b)-capSlack lam d.S q+b*(1-b)/(lam-q)=H := by
    rw [hscore]
    ring
  rw [hs,←hvalue] at hh
  exact hh

end OptimalG.Variational
