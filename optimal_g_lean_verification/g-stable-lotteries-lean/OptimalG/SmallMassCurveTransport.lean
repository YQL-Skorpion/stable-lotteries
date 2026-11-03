import OptimalG.SmallMassTransport
import OptimalG.DefectBounds

/-! C.4 transport applied to the actual verifier primitive. Numerical inputs
are the four rate corners and a score ceiling at minimizing ranks. The score
and primitive estimates used by the transport follow from curve geometry. -/
namespace OptimalG
open Set
namespace VerifierCurve
variable {phi : ℝ → ℝ} {lam : ℝ} (h : VerifierCurve phi lam)
include h

/-- The supporting infimum satisfies both common-target supporting inequalities,
including the zero-score endpoint. -/
theorem supportMinimum_supports {m x : ℝ} (hm : lam<m) (hx : x ∈ Icc 0 lam) :
    x+supportMinimum phi lam m*phi x≤m := by
  rcases lt_or_eq_of_le hx.2 with hxl | hxl
  · have hh := supportMinimum_le_ratio h.lam_pos
      (h.continuous.mono (Icc_subset_Icc le_rfl h.lam_lt_one.le)) h.at_lam
      (fun y hy => h.positive hy) hm ⟨hx.1,hxl⟩
    have hm' := (le_div_iff₀ (h.positive ⟨hx.1,hxl⟩)).mp hh
    linarith
  · rw [hxl,h.at_lam,mul_zero,add_zero]
    exact hm.le

/-- A coefficient from an already verified stored layer is no larger than
our supporting infimum. This allows that stored layer to initialize transport. -/
theorem le_supportMinimum_of_support {m eta : ℝ} (hm : lam<m)
    (hs : ∀ x ∈ Icc 0 lam,x+eta*phi x≤m) : eta≤supportMinimum phi lam m := by
  obtain ⟨_,x,hx,hmin,_⟩ := supportMinimum_attained h.lam_pos
    (h.continuous.mono (Icc_subset_Icc le_rfl h.lam_lt_one.le)) h.at_lam
    (fun y hy => h.positive hy) hm
  rw [hmin]
  apply (le_div_iff₀ (h.positive hx)).mpr
  have hh := hs x ⟨hx.1,hx.2.le⟩
  linarith

theorem smallMass_endpoint_of_stored {beta m : ℝ → ℝ} {p z eta : ℝ}
    (hm : lam<m p) (hz : z ∈ Icc lam 1)
    (hs : ∀ x ∈ Icc 0 lam,x+eta*phi x≤m p)
    (ht : z-lam+beta p*packingK phi p 0 z+eta*phi z≤0) :
    smallMassPsi (curvePrimitive phi) phi beta m lam p z≤0 := by
  have hh := mul_le_mul_of_nonpos_right (h.le_supportMinimum_of_support hm hs)
    (h.nonpositive hz)
  have hK : packingK phi p 0 z=curvePrimitive phi (z-p)-curvePrimitive phi z := by
    simp [packingK,curvePrimitive]
  rw [hK] at ht
  unfold smallMassPsi
  linarith

/-- The high-rank fall condition bounds the score defect by λ. -/
theorem scoreDefect_mem {z : ℝ} (hz : z ∈ Icc lam 1) :
    scoreDefect phi lam z ∈ Icc 0 lam := by
  have hh := h.high_fall z 1 hz.1 hz.2 le_rfl
  rw [h.at_one] at hh
  exact ⟨h.scoreDefect_nonneg ⟨h.lam_pos.le.trans hz.1,hz.2⟩,by
    dsimp [scoreDefect]; linarith⟩

/-- The four corner tests imply the actual adjusted derivative bound; the
primitive cap and high concavity supply all deficit geometry internally. -/
theorem smallMass_adjusted_derivative_nonneg {S zminus p beta b dm A z : ℝ}
    (hc : ConcaveOn ℝ (Icc lam 1) phi) (ha : lam≤zminus)
    (hz : z ∈ Icc zminus 1) (hp : 0≤p) (hpz : p≤z)
    (hstart : curvePrimitive phi zminus=Variational.quadratic lam zminus-S)
    (hzero : phi zminus=lam-zminus)
    (hshift : curvePrimitive phi (z-p)≤Variational.quadratic lam (z-p)-S)
    (hbeta : 0≤beta) (hb : b≤0)
    (h00 : 0≤smallMassRate lam zminus p beta b (-dm/A) zminus 0)
    (h01 : 0≤smallMassRate lam zminus p beta b (-dm/A) zminus lam)
    (h10 : 0≤smallMassRate lam zminus p beta b (-dm/A) 1 0)
    (h11 : 0≤smallMassRate lam zminus p beta b (-dm/A) 1 lam) :
    0≤b*(curvePrimitive phi (z-p)-curvePrimitive phi z)-beta*phi (z-p)+(dm/A)*phi z := by
  have he := h.scoreDefect_mem ⟨ha.trans hz.1,hz.2⟩
  have hrate := smallMassRate_nonneg hz he h00 h01 h10 h11
  have hd := h.primitiveDefect_le_triangle hc ha hz.1 hz.2 hstart hzero
  have hK : curvePrimitive phi (z-p)-curvePrimitive phi z≤
      p*(z-lam)-p^2/2+primitiveDefect phi lam S z := by
    dsimp [primitiveDefect,Variational.quadratic]
    dsimp [Variational.quadratic] at hshift
    nlinarith
  have hl := h.ceiling (z-p) ⟨sub_nonneg.mpr hpz,by linarith [hz.2]⟩
  have hh := smallMassRate_le_derivative (a := -dm/A) hbeta hb hK
    (show phi (z-p)≤lam-z+p by linarith) (show phi z=lam-z-scoreDefect phi lam z by
      simp only [scoreDefect]; ring) hd
  have heq : -( -dm/A)*phi z=(dm/A)*phi z := by ring
  have hh' := hrate.trans hh
  convert hh' using 1 <;> first | rfl | ring

/-- Transport the stored endpoint's third test over a small-mass interval.
No differentiable minimizing-rank selection is needed. -/
theorem smallMass_third_transport {beta m db dm : ℝ → ℝ} {S zminus A left right z : ℝ}
    (hc : ConcaveOn ℝ (Icc lam 1) phi) (ha : lam≤zminus)
    (hz : z ∈ Icc zminus 1) (hlr : left≤right) (hl : 0<left) (hr : right<zminus)
    (hstart : curvePrimitive phi zminus=Variational.quadratic lam zminus-S)
    (hzero : phi zminus=lam-zminus)
    (hshift : ∀ p ∈ Icc left right,
      curvePrimitive phi (z-p)≤Variational.quadratic lam (z-p)-S)
    (htarget : ∀ p ∈ Icc left right,lam<m p)
    (hanti : AntitoneOn m (Icc left right))
    (hA : ∀ p ∈ Icc left right,∀ x ∈ Ico 0 lam,
      supportMinimum phi lam (m p)=(m p-x)/phi x → phi x≤A)
    (hbetac : ContinuousOn beta (Icc left right)) (hmc : ContinuousOn m (Icc left right))
    (hbetad : ∀ p ∈ Ioo left right,HasDerivAt beta (db p) p)
    (hmd : ∀ p ∈ Ioo left right,HasDerivAt m (dm p) p)
    (hbeta : ∀ p ∈ Ioo left right,0≤beta p) (hb : ∀ p ∈ Ioo left right,db p≤0)
    (hcorners : ∀ p ∈ Ioo left right,
      0≤smallMassRate lam zminus p (beta p) (db p) (-dm p/A) zminus 0 ∧
      0≤smallMassRate lam zminus p (beta p) (db p) (-dm p/A) zminus lam ∧
      0≤smallMassRate lam zminus p (beta p) (db p) (-dm p/A) 1 0 ∧
      0≤smallMassRate lam zminus p (beta p) (db p) (-dm p/A) 1 lam)
    (hend : smallMassPsi (curvePrimitive phi) phi beta m lam right z≤0) :
    ∀ p ∈ Icc left right,
      z-lam+beta p*packingK phi p 0 z+supportMinimum phi lam (m p)*phi z≤0 := by
  have hsub (p : ℝ) (hp : p ∈ Icc left right) : z-p ∈ Ioo (0:ℝ) 1 := by
    constructor <;> linarith [hz.1,hz.2,hp.1,hp.2]
  have hJc : ContinuousOn (fun p => curvePrimitive phi (z-p)) (Icc left right) := by
    apply h.primitive_continuous.comp (continuous_const.sub continuous_id).continuousOn
    intro p hp
    exact ⟨(hsub p hp).1.le,(hsub p hp).2.le⟩
  have htransport := smallMassPsi_nonpos_of_adjusted_rate h.lam_pos
    (h.continuous.mono (Icc_subset_Icc le_rfl h.lam_lt_one.le)) h.at_lam
    (fun x hx => h.positive hx) hlr htarget hanti
    (h.nonpositive ⟨ha.trans hz.1,hz.2⟩) hA hbetac hmc hJc hbetad hmd
    (fun p hp => h.primitive_hasDerivAt (hsub p ⟨hp.1.le,hp.2.le⟩))
    (fun p hp => h.smallMass_adjusted_derivative_nonneg hc ha hz
      (by linarith [hp.1]) (by linarith [hp.2,hz.1]) hstart hzero
      (hshift p ⟨hp.1.le,hp.2.le⟩) (hbeta p hp) (hb p hp)
      (hcorners p hp).1 (hcorners p hp).2.1 (hcorners p hp).2.2.1 (hcorners p hp).2.2.2) hend
  intro p hp
  simpa only [smallMassPsi,packingK,add_zero,curvePrimitive,intervalIntegral.integral_same,sub_zero]
    using htransport p hp

end VerifierCurve
end OptimalG
