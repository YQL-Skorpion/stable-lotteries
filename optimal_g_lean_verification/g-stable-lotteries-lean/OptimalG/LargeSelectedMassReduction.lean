import OptimalG.LargeMassFlatEnvelope
import OptimalG.MixedDeficitReduction

/-! The mass derivative of the selected-rank mixed numerator. A continuous
piecewise primitive envelope will use the same comparison on each branch. -/
namespace OptimalG
open Set Variational

noncomputable def largeSelectedNumerator (lam S z q e lower : ℝ) (upper : ℝ→ℝ) (p : ℝ) : ℝ :=
  (p-q)*(p*(z-lam)-p^2/2+S)+p*(upper (z-p+q)-lower)-
    (quadratic lam p-S-p*(z-391/500)/2)*e

noncomputable def largeSelectedMassDerivative
    (lam S p z q e upper lower slope : ℝ) : ℝ :=
  (p*(z-lam)-p^2/2+S)+(p-q)*(z-lam-p)+upper-lower-p*slope+
    (p-lam+(z-391/500)/2)*e

theorem largeSelectedNumerator_hasDerivAt {lam S p z q e lower du : ℝ} {upper : ℝ→ℝ}
    (hu : HasDerivAt upper du (z-p+q)) :
    HasDerivAt (largeSelectedNumerator lam S z q e lower upper)
      (largeSelectedMassDerivative lam S p z q e (upper (z-p+q)) lower du) p := by
  have ha : HasDerivAt (fun t : ℝ=>t*(z-lam)-t^2/2+S) (z-lam-p) p := by
    convert! (((hasDerivAt_id p).mul_const (z-lam)).sub
      (((hasDerivAt_id p).pow 2).div_const 2)).add_const S using 1 <;> (try simp only [id_eq]) <;> ring
  have hb : HasDerivAt (fun t : ℝ=>upper (z-t+q)) (-du) p := by
    convert! hu.comp p (((hasDerivAt_id p).const_sub z).add_const q) using 1 <;> (try simp only [id_eq]) <;> ring
  have hc : HasDerivAt (fun t : ℝ=>quadratic lam t-S-t*(z-391/500)/2)
      (lam-p-(z-391/500)/2) p := by
    convert! ((quadratic_hasDerivAt lam p).sub_const S).sub
      (((hasDerivAt_id p).mul_const (z-391/500)).div_const 2) using 1 <;> (try simp only [id_eq]) <;> ring
  convert! ((((hasDerivAt_id p).sub_const q).mul ha).add
    ((hasDerivAt_id p).mul (hb.sub_const lower))).sub (hc.mul_const e) using 1 <;>
    dsimp [largeSelectedNumerator,largeSelectedMassDerivative] <;> ring

/-- A scalar upper bound on each mass-derivative branch. The sign of the
coefficient of e is established before its upper bound is substituted. -/
theorem largeSelectedMassDerivative_le {lam S p z q e U L du b C D : ℝ}
    (hp : 0≤p) (hlp : lam≤p) (hb : b≤p) (hq : q≤b)
    (hz : z∈Icc (391/500:ℝ) (7/8)) (hneg : 7/8-lam-p≤0)
    (hU : U≤D) (hL : 0≤L) (hd : -du≤C) (he : e≤13/200) :
    largeSelectedMassDerivative lam S p z q e U L du≤
      (p*(7/8-lam)-p^2/2+S)+(p-b)*(7/8-lam-p)+D+p*C+
        (p-lam+93/2000)*(13/200) := by
  have hA := mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2 lam) hp
  have hq0 : 0≤p-q := sub_nonneg.mpr (hq.trans hb)
  have hT1 := mul_le_mul_of_nonneg_left
    (show z-lam-p≤7/8-lam-p by linarith only [hz.2]) hq0
  have hT2 := mul_le_mul_of_nonpos_right
    (show p-b≤p-q by linarith only [hq]) hneg
  have hD := mul_le_mul_of_nonneg_left hd hp
  have hc : 0≤p-lam+(z-391/500)/2 := by linarith only [hlp,hz.1]
  have hE1 := mul_le_mul_of_nonneg_left he hc
  have hE2 := mul_le_mul_of_nonneg_right
    (show p-lam+(z-391/500)/2≤p-lam+93/2000 by linarith only [hz.2])
    (show (0:ℝ)≤13/200 by norm_num)
  unfold largeSelectedMassDerivative
  nlinarith only [hA,hT1,hT2,hU,hL,hD,hE1,hE2]

end OptimalG
